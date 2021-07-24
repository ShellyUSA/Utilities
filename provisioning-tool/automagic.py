######################################################################################################################
#
#  IoT Device Provisioning Script
#  Author: Kerry Clendinning
#  Copyright (c) 2021 Allterco Robotics US
#  Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
#  in compliance with the License. You may obtain a copy of the License at:
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software distributed under the License is distributed
#  on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License
#  for the specific language governing permissions and limitations under the License.
#
#  Shelly is the Trademark and Intellectual Property of Allterco Robotics Ltd.
#
######################################################################################################################
#
#  tl;dr: Run the program with "features" or "help" to learn more
#
#  ex: python automagic.py features
#
######################################################################################################################
#
#  Changes:
#
# 1.0006     
#
# 1.0005     Added --access ALL|Periodic|Continuous features for probe-list and apply to work with
#            battery-powered devices with periodic WiFi access
#
# 1.0004     apply operation now updates settings in db
#            apply now takes --settings argument
#
# 1.0003   - filter some settings from the copy operation during a replace, including "fw" which isn't settable
#            added LatLng and TZ to import and provision-list
#            added --settings to support Lat/Lng with simple provision operation
#            improved error handling of timeouts during factory-reset
#
# 1.0002   - fixed IP address by re-getting status in provision_list()
#            fixed some python3 compatibility issues
#            re-fetch settings after device name changes in provision()/provision_list()
#            added identify operation
#            added --restore option to apply
#            added Gateway to import column options
#            better query columns expansion e.g. wifi_sta.gw will now match settings.wifi_sta.gw
#            added replace operation
#
######################################################################################################################
#
#  TODO:
#            Check Shelly firmware version (for LATEST)
#            OTA update settings/status after complete (or fix this)
#
#            make provision-list work without dd-wrt... rename provision_list and provision to provision_ddwrt and provision_native(?)
#            make --settings work with provision-list and provision-settings, as defaults(?)
#
#  NICE-TO-HAVES:
#            Insure it's a 2.4GHz network
#            mDNS discovery?
#            OTA from local webserver
#            --ota-version-check=required|skip|try (in case redirect/forwarding would fail)
#
#            apply-list(?)  to apply --settings or --url to probe-list devices, instead of db
#            Simplify some python2/3 compatibility per: http://python-future.org/compatible_idioms.html
#            DeviceType -- limit provision-list to matching records -- provision-list to choose devices by DeviceType
#            -U option to apply operation to make arbitray updates in device DB (for use prior to restore)
#            --parallel=<n>  batched parallel firmware updating, n at a time, pausing between batches, or exiting if no more
#            --group for "provision" -- add to group
#            --prompt n,n,n  for use with "provision" to prompt for v,v,v giving individual values like StaticIP
#            Access=Continuous/Periodic -- to indicate which devices shouldn't be expected online
#
#  FUTURE:
#            my.shelly.cloud API integration?
#
######################################################################################################################


from __future__ import print_function
from __future__ import absolute_import
import sys
import os
import re
import time
import json
import argparse
import subprocess
import binascii
import tempfile
import zipfile
import telnetlib
import base64
import getpass
from textwrap import dedent
import csv
import timeit
import importlib
import collections
import copy
import socket

if sys.version_info.major >= 3:
    import urllib.request
    import urllib.parse
    import requests
    from io import BytesIO
    import collections.abc
    from urllib.parse import urlencode, quote_plus, quote
    from urllib.error import URLError, HTTPError
else:
    from urllib import urlencode
    input = raw_input
    import urllib2
    import urllib
    from StringIO import StringIO
    from urllib2 import HTTPError

version = "1.0006"

required_keys = [ 'SSID', 'Password' ]
optional_keys = [ 'StaticIP', 'NetMask', 'Gateway', 'Group', 'Label', 'ProbeIP', 'Tags', 'DeviceName', 'LatLng', 'TZ', 'Access' ]
default_query_columns = [ 'type', 'Origin', 'IP', 'ID', 'fw', 'has_update', 'settings.name' ] 

all_operations = ( 'help','features','provision-list','provision','factory-reset','flash','import', 'ddwrt-learn','list', 'clear-list','print-sample','probe-list', 'query', 'apply', 'schema', 'identify', 'replace' )

exclude_setting = [ 'unixtime', 'fw', 'time', 'hwinfo', 'build_info', 'device', 'ison', 'has_timer', 'power', 'connected',
        'ext_humidity','ext_switch','ext_sensors','ext_temperature',    #TODO  -- parameter
        'actions',                                                      # handled differently
        'schedule','schedule_rules',                                    # handled differently
        'login','wifi_sta','wifi_sta1','wifi_ap' ]                      # not allowing these, for now, because of password not being present

exclude_from_copy = [ 'actions.names','alt_modes','build_info','calibrated','device.mac','device.hostname','device.num_emeters','device.num_inputs',
                      'device.num_meters','device.num_outputs','device.num_rollers','device.type','fw','hwinfo.batch_id','hwinfo.hw_revision',
                      'unixtime','settings.meters','settings.fw_mode','settings.login.default_username' ]

init = None
connect = None
reconnect = None
urlquote = None
deep_update = None
url_read = None
http_post = None
os_stash = {}
stringtofile = None
router_db = None
device_db = None
device_queue = None
factory_device_addr = "192.168.33.1"
labelprinting = None

####################################################################################
#   Help subsystem
####################################################################################

def help_features( ):
    print(dedent(""" 
                 Features:

                 Automatically locates new devices that are in the factory reset state ready to configure.
                 Each located device can be added to the local WiFi network, using the "provision" operation,
                 or added to a specific other WiFi network, using the "provision-list" operation.
                 
                 With provision-list, one or two spare DD-WRT routers are used as the client connection and
                 WiFi access point, automatically configured at each step to match network SSID of the factory
                 reset Shelly and the target SSID and credentials specified in a list of instructions given to
                 the program.  Note that with two DD-WRT devices, the process is much faster, able to provision
                 1 to 2 target devices per minute.
                 
                 When using the provision operation, your computer or laptop will change from one WiFi network 
                 to another (to connect to the target device's WiFi hotspot to configure it).  Using provision-list,
                 instead, will mean no loss of WiFi connectivity on your computer, since instructions are sent
                 to a DD-WRT device to set the WiFi SSID instead.  The provision-list operation is generally twice 
                 as fast as provision.

                 There are commands to work with the set of instructions used by provision-list, to import, view 
                 and clear the list: "import," "list," and "clear-list".
                 
                 The provision operation supports only DHCP, while provision-list can setup devices with either
                 DHCP or static IP addresses.  Either operation can additionally command each newly provisioned
                 device to take an OTA firmware update to the LATEST or a specific version of software.
                 
                 With provision-list there are many additional features, including setting the name of the device
                 as it shows up in the UI and in the settings web UI.  (Other settings like lat/long can be easily
                 added in the future.)  The imported list of instructions can include a "Group" column, which 
                 then allows provision-list to work on a specific set of instructions instead of the entire queue.
                 A mechanism for automatically printing labels, given a small program provided by the user is
                 available with both provision and provision-list, but additional attributes like "Label" can be 
                 added to the imported instructions for provision-list.
                 
                 There is a "factory-reset" operation which makes it easy to return a device to factory settings,
                 given it is on the local WiFi network, and the "flash" operation instructs local devices to take
                 an OTA firmware update.

                 Additionally, existing devices on the local WiFi network can be probed using the "probe-list" command
                 to discover all of their settings and status.  For battery-powered devices that are only periodically
                 available on the network, the attribute Access=Periodic lets probe-list run for an extended period of 
                 time looking frequently for the devices.  A powerful "query" operation can report on any information 
                 found in the probe.  The "apply" operation allows programming the discovered devices with OTA firmware 
                 updates, as well as making arbitrary settings changes using the --url option.

                 An "identify" operation is available to continually toggle on/off a light or relay, given an IP
                 address, in order to aid in identifying a device.  Useful, for instance, with multiple light bulbs
                 in a lighting fixture.

                 The settings from one device can be copied to a new replacement device using the "replace" operation.
                 Having transfered the settings, it is then possible to use "apply" with --restore to reprovision the
                 replacement device.
                 """) )

def help_operations( ):
    print(dedent(""" 
                 usage: python automagic.py [options] OPERATION

                 OPERATION is one of: help, provision-list, provision, factory-reset, flash, ddwrt-learn, import, 
                                      list, clear-list, print-sample, probe-list, query, apply

                 More detailed information will follow a short description of all of these operations.

                 help               - shows this help guide
                 features           - gives a short explanation of the features of this utility

                 provision          - configure any device(s) found in factory mode onto the current WiFi network

                 import             - import list of instructions for programming with provision-list
                 list               - shows the contents of the imported list of instructions
                 clear-list         - erases the imported instructions for "list" operations
                 provision-list     - configure devices found in factory reset mode onto a list of specified WiFi networks
                 probe-list         - discovers information about devices in the import list (they must specify ProbeIP addresses)

                 ddwrt-learn        - learn identity and settings of dd-wrt devices for use with provision-list
                 factory-reset      - factory reset a device
                 flash              - OTA (over the air) flash new firmware onto a device
                 print-sample       - sends a sample device info record to the custom label printing module (see --print-using)
                 query              - list information from the device database formed from provisioning and probing operations
                 apply              - apply --ota, --url and --settings to devices matching a query from the device database
                 identify           - toggle power on/off on a given device to identify (by ip-address)
                 replace            - copy the settings of one device to another in the device database

                 Note that it is inadvisable to run multiple copies of this program while new devices are being
                 powered on to configure.  The program will automatically detect any new device and might attempt
                 to program it from two instances if run on multiple computers simultaneously.
                """))


def more_help( ):
    print(dedent(""" 

                 More help is available for each operation above. Try "help provision" or "help features".
                 You can also try "help all".
                """))

def help_commands( ):
    help_operations( )

def help_help( ):
    print(dedent(""" 
                 help
                 ----
                 Prints the text you are reading now.  Additional help for each operation is available.  Try "help provision" for example.
                 To see all help, try "help all".  An overview of the program's functionalities is available too: "help features".
                """))

def help_provision( ):
    print(dedent(""" 
                 provision
                 ---------
                 The provision operation is used to provision devices to attach to the same WiFi network used by the laptop (or desktop)
                 computer where the program is run.  Its functionality is limited in comparison to the provision-list operation, since all
                 discovered devices will be attached to the same local network.

                     --ssid (required)           SSID of the local WiFi network.

                     --wait-time                 Time to wait on each pass looking for new devices, 0 for just once

                     --ota PATH                  Apply OTA update of firmware after provisioning. PATH should specify an http path to
                                                 the firmware, or "LATEST".

                     --ota-timeout (-n)          Time in seconds to wait on OTA udpate. Default 300 (5 minutes).

                     --prefix STRING             SSID prefix applied to discovering new devices (default: shelly)

                     --time-to-pause (-p)        Time to pause after various provisioning steps

                     --toggle                    After each device is provisioned, toggle it on/off repeatedly until it is unplugged.

                     --cue                       After each device is provisioned, wait for the user to press enter before continuing.

                     --print-using PYTHON-FILE   For each provisioned device, call a function "make_label," passing all information about
                                                 the newly provisioned device as a python dict, as the single argument to make_label().

                                                 ex: def make_label( dev_info ):
                                                         print( repr( dev_info ) )

                     --settings N=V,N=V...       Supply LatLng or other values to apply during provisioning step.  Supported attributes:
                                                 DeviceName, LatLng, TZ
                """))

def help_provision_list( ):
    print(dedent(""" 
                 provision-list
                 --------------
                 List provisioning is ideal for pre-configuring a large number of IoT devices intended to be deployed on different WiFi
                 networks. An imported list of SSIDS will determine for which networks the devices will be provisioned.

                 In order to configure and verify each device, making sure it is able to connect to its target SSID, a spare DD-WRT 
                 router is used to temporarily create a network with the proper SSID and credentials.

                     ex: python automagic.py -N myddwrt provision-list

                 Before using provision-list, some setup work is required. See ddwrt-learn and import command descriptions.

                 Options for use with provision-list:

                     --ddwrt-name (-N)           This required option specifies the name of a dd-wrt device, as learned 
                                                 with the ddwrt-learn command.  The dd-wrt device will be used to configure 
                                                 the target IoT devices.

                                                 A second instance of this same option can be used to identify a second dd-wrt
                                                 device for use during the provisioning operation.  This will speed up the
                                                 operation by over 2X.  When two dd-wrt devices are available, there is no need to 
                                                 switch a single device between AP and client modes, which is a time-consuming
                                                 process.  It is highly recommended to use the two-device configuration.

                     --group (-g) GROUP          Limit the operation to the set of instructions imported with the given "Group" ID.
                                                 If --group/-g is not specified, ALL imported instructions will be used.

                     --time-to-wait (-w) SECS    Time to wait between each pass before looking for more new devices.

                     --prefix STRING             Prefix for SSID search. Defaults to "shelly".

                     --verbose (-v)              Give verbose logging output (repeating -v increases verbosity).

                     --ota PATH                  Apply OTA update of firmware after provisioning. PATH should specify an http path to
                                                 the firmware, or "LATEST".

                     --ota-timeout (-n)          Time in seconds to wait on OTA udpate. Default 300 (5 minutes).

                     --device-db FILE.json       This file will hold information about each device that has been provisioned or probed.

                     --device-queue FILE.json    Specifies the name of the .json file that has the list of devices queued up by the
                                                 import command. The default name is provisionlist.json.

                     --ddwrt-file FILE.json      File to contains definitions of dd-wrt devices created using the --ddwrt-learn 
                                                 command.  The default is ddwrt_db.json.

                     --timing                    Show timing of steps during provisioning.

                     --toggle                    After each device is provisioned, toggle it on/off repeatedly until it is unplugged.

                     --cue                       After each device is provisioned, wait for the user to press enter before continuing.

                     --print-using PYTHON-FILE   For each provisioned device, call a function "make_label," passing all information about
                                                 the newly provisioned device as a python dict, as the single argument to make_label().

                                                 ex: def make_label( dev_info ):
                                                         print( repr( dev_info ) )

                     --prefix STRING             SSID prefix applied to discovering new devices (default: shelly)

                     --time-to-pause (-p)        Time to pause after various provisioning steps
                """))

def help_ddwrt_learn( ):
    print(dedent(""" 
                 ddwrt-learn
                 -----------
                 Set up a DD-WRT router in access point mode, with DHCP server disabled, telnet enabled.  Use the username "admin"
                 and choose a password you are okay with storing in plaintext for use by this program. Static wan 
                 address 192.168.33.10, gateway 192.168.33.1, subnet mask 255.255.255.0

                 IMPORTANT: On setup page, disable DHCP, enable forced DNS redirection, and on 
                 Services page, disable Dnsmasq entirely.

                 When the device is configured, run ddwrt-learn.

                      ex: python automagic.py ddwrt-learn -N sh1 -p all4shelly -e 192.168.1.1

                 Change the device WiFi setting to client mode and repeat.

                 This has been tested with Broadcom-based (Linksys) routers.

                 Options for use with provision-list:

                     --ddwrt-name (-N)           Name of device to learn.  (required)

                     --ddwrt-file                File to contains definitions of dd-wrt devices created using the --ddwrt-learn 
                                                 command.  The default is ddwrt_db.json

                     --ddwrt-address (-e)        IP address of dd-wrt device to learn about.  (required)

                     --ddwrt-password (-p)       Root password for dd-wrt device.  (required)
                """))

def help_import( ):
    print(dedent(""" 
                 import
                 ------
                 The import command adds instructions to the queue of operations the provision-list command will perform.

                     ex: python automagic.py import --file /tmp/sample.csv

                 Options for use with import: 

                     --file (-f)                 File containing instructions to import. May be .csv or .json (required).

                 There are many possible fields to include in the .csv (or .json) input file.  Only two are required: SSID
                 and Password.  Here is an example of the simplest possible instructions:

                     $ cat /tmp/sample.csv
                     SSID,Password
                     TestNet,abc12cd34
                     OtherNet,zzaabb33

                 The example above would create instructions to program the next two devices discovered via 
                 provision-list with the credentials specified.

                 Optional fields are: StaticIP, NetMask, Gateway, Group, Label, ProbeIP, and Tags.

                     DeviceName                  If specified, the value name of the device will be set.  (settings/name)

                     StaticIP                    Static IP address to assign to the device.  This will disable DHCP and define
                                                 a static address directly to the device.  You must make provisions with the 
                                                 network router to reserve static IP address and insure they are unique to each
                                                 device.  If StaticIP is included, a NetMask must also be specified.

                     NetMask                     A NetMask must be included when a StaticIP is set.  The NetMask determines what
                                                 IP addresses are on the local subnet vs. routed.

                     Gateway                     A Gateway shoule be included when a StaticIP is set.  It is needed for the device
                                                 to reach any services like sntp, to get the time, or to download OTA updates.

                     LatLng                      Latitude and longitude, for sunrise/sunset calculations, in the form lat:lng,
                                                    ex: 30.33658:-97.77775

                     TZ                          Timezone info, in the form tz_dst:tz_dst_auto:tz_utc_offset:tzautodetect, 
                                                    ex: False:True:-14400:True

                     Group                       A Group can be assigned to an imported record, and later used to select a subset
                                                 of records for operations like provision-list.  See the --group option.

                     Tags                        A set of comma-delimited tags can be assigned to an imported record and used in 
                                                 a similar fashion to the "Group" field.  See the --match-tag option. This field
                                                 must be quoted if it contains commas.

                     Label                       The Label field is useful with the feature for printing a label when each device
                                                 is provisioned.  It is a free-form text field.  See --print-using option, and
                                                 print-sample operation.

                     ProbeIP                     Devices already on the local network, not needing provisioning, can be imported
                                                 and managed using this program.  To import devices, set the ProbeIP to the device's
                                                 IP address and use the probe-list operation.

                     Access                      Defines whether a device should be expected on the network continually, or, like
                                                 some battery powered devices, only periodically. Values: Continuous or Periodic.
                                                 Works in conjunction with ProbeIP and the probe-list operation to find periodic 
                                                 devices which take much longer to discover.
                """))

def help_list( ):
    print(dedent(""" 
                 list
                 ----
                 The list operator prints the pending operations in the device queue, imported using the import operation, and
                 consumed using provisision-list.

                     --group (-g) GROUP          Limit the operation to the set of instructions imported with the given "Group" ID.
                                                 If --group/-g is not specified, ALL imported instructions will be listed.
                """))

def help_clear_list( ):
    print(dedent(""" 
                 clear-list
                 ----------
                 Erase the entire list of pending operations.
                """))

def help_probe_list( ):
    print(dedent(""" 
                 probe-list
                 ----------
                 The probe-list operation gathers information about devices queued using the import command, with the ProbeIP field 
                 specifying their IP addresses existing on the local network. 

                     --query-conditions          Use query-conditions to filter the devices that will be probed.  The query-conditions 
                                                 option is a comma-delimited list of name=value pairs.

                     --group (-g) GROUP          Limit the operation to the set of instructions imported with the given "Group" ID.
                                                 If --group/-g is not specified, ALL imported instructions will be probed.

                     --match-tag (-t)            Limit the query operation to devices with a selected tag.

                     --access Periodic|ALL|Co... Only probe devices that with Access=Continuous (default), Periodic, or ALL

                     --refresh                   Refresh the db with attributes for all previously probed devices, rather than 
                                                 using the import command.
                """))

def help_query( ):
    print(dedent(""" 
                 query
                 -----
                 Print information about devices in the device database.  The device database is comprised of all devices that have
                 been provisioned by the provision-list operation, and any imported using the probe-list operation.

                     --query-columns             A comma-delimited list of columns to display. To learn what columns are available,
                                                 use the schema operation.

                     --query-conditions          Use query-conditions to filter the devices reported by the query operation.  The
                                                 query-conditions option is a comma-delimited list of name=value pairs.  Use the
                                                 schema operation to list the available columns.

                     --group (-g) GROUP          Limit the operation to the set of devices with the given "Group".

                     --match-tag (-t)            Limit the query operation to devices with a selected tag.

                     --set-tag (-T)              Add a specified tag to each selected device.

                     --delete-tag                Delete a specified tag from each selected device.

                     --refresh                   Refresh status and settings stored in the device DB for queried devices.
                """))

def help_schema( ):
    print(dedent(""" 
                 schema
                 ------
                 The schema operaion displays the column list available for query-conditions and query-columns.  It scans the device 
                 database that consists of all devices discovered using the provision-list and probe-list operations.

                     --query-conditions          Use query-conditions to filter the devices reported by the schema operation.  The
                                                 query-conditions option is a comma-delimited list of name=value pairs.

                     --query-columns             A comma-delimited list of columns to match.

                     --group (-g) GROUP          Limit the operation to the set of devices with the given "Group".

                     --match-tag                 Limit the schema operation to devices with a selected tag.
                """))

def help_apply( ):
    print(dedent(""" 
                 apply
                 -----
                 The apply operation is used to apply OTA updates or other settings to devices in the device database.  It functions
                 like the query command, plus additional options: --ota and --url.

                     --query-conditions          Use query-conditions to filter the devices affected by the apply operation.  The
                                                 query-conditions option is a comma-delimited list of name=value pairs.

                     --query-columns             A comma-delimited list of columns to display. To learn what columns are available,
                                                 use the schema operation.

                     --group (-g) GROUP          Limit the operation to the set of instructions imported with the given "Group" ID.

                     --match-tag (-t)            Limit the query operation to devices with a selected tag.

                     --set-tag (-T)              Add a specified tag to each selected device.

                     --delete-tag                Delete a specified tag from each selected device.

                     --ota PATH                  Apply OTA update of firmware after provisioning. PATH should specify an http path to
                                                 the firmware, or "LATEST".

                     --ota-timeout (-n)          Time in seconds to wait on OTA udpate. Default 300 (5 minutes).

                     --time-to-pause (-p)        Time to pause after various provisioning steps

                     --delete-device DEVICE-ID   Provide device ID or "ALL" to delete queries devices from the device db.

                     --restore-device DEVICE-ID  Restores specified device, or with "ALL," those matching the -Q query to their settings
                                                 stored in the device db.

                     --url                       The --url option specifies an URL fragment like "/settings/?lat=31.32&lng=-98.324" to 
                                                 be applied to each matching device.  The --url option can be repeated multiple times.  
                                                 The Device IP will be prefixed to each specified URL fragment to produce a complete URL 
                                                 like "http://192.168.1.10//settings/?lat=31.32&lng=-98.324"

                     --settings N=V,N=V...       Supply LatLng or other values to apply to all matching devices.  Supported attributes:
                                                     DeviceName, LatLng, TZ

                     --dry-run                   When used with --restore-device, --url, and --settings, displays, rather than executes, 
                                                 the steps (urls) which would be applied to each matching device.

                     --refresh                   Refresh status and settings stored in the device DB for queried devices.  (Automatically
                                                 applied after any --url, or --settings operation not specifying --dry-run.)

                     --access Periodic|ALL|Co... Only apply changes to devices that with Access=Continuous (default), Periodic, or ALL
                """))

def help_factory_reset( ):
    print(dedent(""" 
                 factory-reset
                 -------------
                 Performs a factory reset on the specified device.

                     --device-address (required) Address or DNS name of target device
                """))

def help_identify( ):
    print(dedent(""" 
                 identify
                 --------
                 Toggles power on/off on a device to identify which device holds the specified address

                     --device-address (required) Address or DNS name of target device
                """))

def help_flash( ):
    print(dedent(""" 
                 flash  
                 -----
                 The flash operation flashes firmware onto a specified device. (You can also use the --ota option with the "apply" operation
                 to flash multiple devices.)

                     --device-address (required) Address or DNS name of target device

                     --ota PATH                  Apply OTA update of firmware after provisioning. PATH should specify an http path to
                                                 the firmware, or "LATEST".

                     --ota-timeout (-n)          Time in seconds to wait on OTA udpate. Default 300 (5 minutes).

                     --time-to-pause (-p)        Time to pause after various provisioning steps
                """))

def help_print_sample( ):
    print(dedent(""" 
                 print-sample
                 ------------
                 The print-sample operation is used to test the label printing feature and the --print-using option.

                     --print-using PYTHON-FILE   For each provisioned device, call a function "make_label," passing all information about
                                                 the newly provisioned device as a python dict, as the single argument to make_label().

                                                 ex: def make_label( dev_info ):
                                                         print( repr( dev_info ) )
                """))

def help_replace( ):
    print(dedent(""" 
                 replace
                 -------
                 Can be used to copy the settings in the device database from one device to another.  It only affects the settings in
                 the database.  After completing the replace operation, use the --restore option to the apply operation, in order to 
                 reprogram the replacement device.

                     python automagic.py replace --from-device 7FB210446B27 --to-device 537B3C3F8823
                     python automagic.py apply --restore 537B3C3F8823
          
                """))

def help_docs( what ):
    if not what:
        help_operations( )
        more_help( )
    elif what[0] == "all":
        help_operations( )
        help_help( )
        help_provision( )
        help_provision_list( )
        help_ddwrt_learn( )
        help_import( )
        help_list( )
        help_clear_list( )
        help_probe_list( )
        help_query( )
        help_schema( )
        help_apply( )
        help_factory_reset( )
        help_identify( )
        help_flash( )
        help_print_sample( )
        help_replace( )
    else:
        try:
            eval( 'help_' + what[0].replace('-','_') + '()' )
        except:
            print( "No help for " + what[0] )
            print( "Try: help operations, or one of " + ', '.join( all_operations ) )

####################################################################################
#   Python 2/3 compatibility functions
####################################################################################

def v2_url_read( s, mode = 't', tmout = 2 ):
    if mode == 'b':
        return urllib2.urlopen( s, timeout = tmout ).read( )
    return urllib2.urlopen( s, timeout = tmout ).read( ).decode( 'utf8' )

def v3_url_read( s, mode = 't', tmout = 2 ):
    return urllib.request.urlopen( s, timeout = tmout ).read( )

def v2_http_post( url, data, username, password, referrer ):
    post = url_encode( data )
    req = urllib2.Request( url, post )
    base64string = base64.b64encode( '%s:%s' % ( username, password ) )
    req.add_header( "Authorization", "Basic %s" % base64string )
    req.add_header( 'Referer', referrer )
    response = urllib2.urlopen( req )
    return response.read( )

def v3_http_post( url, data, username, password, referrer ):
    return( requests.post( url, data = data, auth = ( username, password ), headers = { 'Referer' : referrer } ) )

def v2_deep_update(d, u):
    for k, v in u.iteritems():
        if isinstance(v, collections.Mapping):
            d[k] = v2_deep_update(d.get(k, {}), v)
        else:
            d[k] = v
    return d

def v3_deep_update(d, u):
    for k, v in u.items():
        if isinstance(v, collections.abc.Mapping):
            d[k] = v3_deep_update(d.get(k, {}), v)
        else:
            d[k] = v
    return d

def noop( a = "" ):
    return( a )

def compatibility( ):
    global url_read, http_post, urlquote, stringtofile, deep_update

    if sys.version_info.major >= 3:
        url_read = v3_url_read
        http_post = v3_http_post
        deep_update = v3_deep_update
        urlquote = urllib.parse.quote
        stringtofile = BytesIO
    else:
        url_read = v2_url_read
        http_post = v2_http_post
        deep_update = v2_deep_update
        urlquote = urllib.quote_plus
        stringtofile = StringIO

####################################################################################
#   PC compatibility functions
####################################################################################

def pc_write_profile( ssid, path ):
    f = open( path, "w" )
    f.write( """<?xml version="1.0"?>
<WLANProfile xmlns="http://www.microsoft.com/networking/WLAN/profile/v1">
        <name>""" + ssid + """</name>
	<SSIDConfig>
		<SSID>
                        <hex>""" + str(binascii.b2a_hex(ssid.encode("utf-8")).decode()) + """</hex>
                        <name>""" + ssid + """</name>
		</SSID>
	</SSIDConfig>
	<connectionMode>manual</connectionMode>
	<MSM>
		<security>
			<authEncryption>
				<authentication>open</authentication>
				<encryption>none</encryption>
				<useOneX>false</useOneX>
			</authEncryption>
		</security>
	</MSM>
	<MacRandomization xmlns="http://www.microsoft.com/networking/WLAN/profile/v3">
		<enableRandomization>false</enableRandomization>
	</MacRandomization>
</WLANProfile>""")
    f.close()

def pc_get_cmd_output(cmd, key, err):
    output = subprocess.check_output( cmd, shell=True ).decode( 'utf8' )
    m = re.search( key + ' *:  *(.*)', output )
    if not m:
         eprint( err )
         sys.exit()
    return m.group(1).rstrip()

def pc_get_cred():
    ssid = pc_get_cmd_output( 'cmd /c "netsh wlan show interfaces | findstr SSID"', 'SSID', "Could not identify current SSID" )
    profile = pc_get_cmd_output( 'cmd /c "netsh wlan show interfaces | findstr Profile"', 'Profile', "Could not identify current Profile" )
    pw = pc_get_cmd_output( 'cmd /c "netsh wlan show profile name=' + ssid + ' key=clear | findstr Key"', 'Key Content', "Could not determine pasword for network " + ssid )
    return { 'profile' : ssid, 'ssid' : ssid, 'password' : pw }

def pc_connect( credentials, str, prefix = False, password = '', ignore_ssids = {}, verbose = 0 ):
    if prefix:
        # it's necessary to disconnect in order to have wlan show networks show all networks
        os.system('cmd /c "netsh wlan disconnect"')
        show_networks = subprocess.check_output( 'cmd /c "netsh wlan show networks"', shell=True ).decode('utf8')
        network = None
        networks = re.findall( r'SSID .*', show_networks, re.MULTILINE )
        if verbose > 1: print(repr(networks))
        for n in networks:
            if verbose > 1: print(repr(n))
            m = re.search( 'SSID  *[0-9][0-9]*  *:  *(' + str + '.*)', n )
            if m and m.group(1) != '' and m.group(1).rstrip() not in ignore_ssids:
                network = m.group(1).rstrip()
                break

        if not network:
            os.system('cmd /c "netsh wlan connect name=' + credentials['profile'] + '"')
            return None
    else:
        network = str

    pc_write_profile( network, tempfile.gettempdir() + r"\ntwrk_tmp.xml" )
    os.system('cmd /c "netsh wlan add profile filename=' + tempfile.gettempdir() + r'\ntwrk_tmp.xml user=all"')

    os.system('cmd /c "netsh wlan connect name=' + network + '"')
    return network

def pc_reconnect( credentials ):
    os.system('cmd /c "netsh wlan connect name=' + credentials['profile'] + '"')
    return True

####################################################################################
#   Mac compatibility functions
####################################################################################

def mac_init( ):
    global os_stash
    import objc
    
    objc.loadBundle('CoreWLAN',
                    bundle_path = '/System/Library/Frameworks/CoreWLAN.framework',
                    module_globals = globals())
    
    os_stash['iface'] = CWInterface.interface()

def mac_get_cred():
    ssid = os_stash['iface'].ssid()
    pw = subprocess.check_output( """security find-generic-password -ga """ + ssid + """ 2>&1 1>/dev/null | sed -e 's/password: "//' -e 's/"$//'""", shell=True ).rstrip()
    if pw == '':
        print( "Could not get wifi password" )
        sys.exit()
    return {'profile' : ssid, 'ssid' : ssid, 'password' : pw.decode("ascii") }

def mac_connect( credentials, str, prefix = False, password = '', ignore_ssids = {}, verbose = 0 ):
    passes = 0
    while passes < 5:
        for i in range( 3 ):
            passes += 1
            if prefix:
                networks, error = os_stash['iface'].scanForNetworksWithSSID_error_(None, None)
            else:
                networks, error = os_stash['iface'].scanForNetworksWithName_error_(str, None)
            if networks:
                break
            time.sleep( 1 )
    
        if verbose > 1: print(repr(networks))
    
        if not networks:
            eprint( error )
            return None
    
        found = None
        
        for n in networks:
            if n.ssid() and ( n.ssid().startswith(str) and prefix or n.ssid() == str ) and n.ssid() not in ignore_ssids:
                found = n
                break

        if found: break

    if not found:
        return None
   
    if found: 
        if verbose > 1: print( 'Detected ' + found.ssid() )
        success, error = os_stash['iface'].associateToNetwork_password_error_(found, password, None)
        if error:
             eprint(error)
             return None
        return found.ssid()
    return None

def mac_reconnect( credentials ):
    return mac_connect( credentials, credentials['ssid'], prefix = False, password = credentials['password'] )

####################################################################################
#   DD-WRT interactions
####################################################################################

def ddwrt_do_cmd( tn, cmd, prompt ):
    tn.read_very_eager()   # throw away any pending junk
    tn.write(b"echo ${z}BOT${z};(" + cmd.encode('ascii') + b")  2>/tmp/cmd.err.out\n")
    tn.read_until(b'####BOT####\r\n',2)     ### consume echo
    response = tn.read_until(prompt,2).decode('ascii')[:-len(prompt)-1]   #remove prompt
    result = []
    err = ""
    for line in response.replace("\r","").split("\n"):
        result.append( line )
    tn.write(b"echo ${z}BOT${z};cat /tmp/cmd.err.out\n")
    tn.read_until(b'####BOT####\r\n',2)     ### consume echo
    err = tn.read_until(prompt,2).decode('ascii')[:-len(prompt)-1]   #remove prompt
    return ( result, err )

def ddwrt_get_single_line_result( cn, cmd ):
    ( result, err ) = ddwrt_do_cmd( cn['conn'], cmd, cn['eot'] )
    if err != "":
        raise Exception( err )
    if len( result ) > 2:
        raise Exception( 'multi-line response' )
    return( result[0] )

def ddwrt_sync_connection( cn, btext, tmout ):
    cn['conn'].write( btext + b"z='####';echo ${z}SYNC${z}\n" )
    cn['conn'].read_until( b'####SYNC####\r\n', tmout )
    cn['conn'].read_until( cn['eot'], tmout )

def ddwrt_establish_connection( address, user, password, eot ):
    tn = telnetlib.Telnet( address )
    tn.read_until( b"login: " )
    tn.write( user.encode( 'ascii' ) + b"\n")
    if password:
        tn.read_until( b"Password: " )
        tn.write( password.encode( 'ascii' ) + b"\n" )
    cn = { 'conn' : tn, 'eot' : eot }
    ddwrt_sync_connection( cn, b"PS1="+eot+b"\\\\n;", 20 )
    return cn

def ddwrt_connect_to_known_router( ddwrt_name ):
    if ddwrt_name not in router_db:
        print( 'dd-wrt device ' + ddwrt_name + ' not found. Use ddwrt-learn, or choose another device that is already known.' )
        sys.exit()
    router = router_db[ ddwrt_name ]
    cn = ddwrt_establish_connection( router[ 'address' ], 'root', router[ 'password' ], b'#EOT#' )
    cn[ 'router' ] = router
    et0macaddr = ddwrt_get_single_line_result( cn, "nvram get et0macaddr" )
    if et0macaddr != router[ 'et0macaddr' ]:
        print( 'device currently at ip address ' + router[ 'address' ] + ' is not ' + ddwrt_name )
        sys.exit( )
    cn[ 'current_mode' ] = ddwrt_get_single_line_result( cn, "nvram get wl_mode" )
    return cn

def ddwrt_apply( address, user, password ):
    data = { 'submit_button':'index', 'action':'ApplyTake' }
    http_post( 'http://' + address + '/apply.cgi', data, user, password, 'http://' + address + '/Management.asp' )

def ddwrt_program_mode( cn, pgm, from_db, deletes=None ):
    for k in pgm.keys():
        ddwrt_get_single_line_result( cn, "nvram set " + k + '=' + pgm[k] )
    mode = pgm[ 'wl_mode' ]
    for k in from_db:
        ddwrt_get_single_line_result( cn, "nvram set " + k + '=' + cn[ 'router' ][ mode ][ k ] )
    if deletes:
        for k in deletes:
            ddwrt_get_single_line_result( cn, "nvram unset " + k )
    ddwrt_get_single_line_result( cn, "nvram commit 2>/dev/null" )
    if cn[ 'current_mode' ] == mode:
        ddwrt_get_single_line_result( cn, "stopservice nas;stopservice wlconf 2>/dev/null;startservice wlconf 2>/dev/null;startservice nas" )
    else:
        cn[ 'current_mode' ] = mode
        ddwrt_apply( cn[ 'router' ][ 'address' ], 'admin', cn[ 'router' ][ 'password' ] )
        print( "changing dd-wrt modes... configuration sent, now waiting for dd-wrt to apply changes" )
        time.sleep( 5 )
        ddwrt_sync_connection( cn, b'', 20 )
        ddwrt_get_single_line_result( cn, "wl radio off; wl radio on" )

def ddwrt_set_ap_mode( cn, ssid, password ):
    pgm = { 'pptp_use_dhcp' : '1',        'wan_gateway' : '0.0.0.0',         'wan_ipaddr' : '0.0.0.0',               
            'wan_netmask' : '0.0.0.0',    'wan_proto' : 'disabled',          'wl0_akm' : 'psk psk2',                 
            'wl0_mode' : 'ap',            'wl0_nctrlsb' : 'none',            'wl0_security_mode' : 'psk psk2',       
            'wl0_ssid' : ssid,            'wl_ssid' : ssid,                  'wl0_wpa_psk' : password,               
            'wl_mode' : 'ap',             'dns_redirect' : '1',              'dnsmasq_enable' : '0'                  
          } 
    from_db = [ 'wl0_hw_rxchain','wl0_hw_txchain','wan_hwaddr' ]
    deletes = [ 'wan_ipaddr_buf','wan_ipaddr_static','wan_netmask_static', 'wl0_vifs' ]
    ddwrt_program_mode( cn, pgm, from_db, deletes )

def ddwrt_set_sta_mode( cn, ssid ):
    pgm = { 'pptp_use_dhcp' : '0',        'wan_gateway' : '192.168.33.1',    'wan_ipaddr' : '192.168.33.10',                     
            'wan_ipaddr_static' : '..',   'wan_netmask' : '255.255.255.0',   'wan_netmask_static' : '..',                     
            'wan_proto' : 'static',       'wl0_akm' : 'disabled',            'wl0_mode' : 'sta',                     
            'wl0_nctrlsb' : '',           'wl0_security_mode' : 'disabled',  'wl0_vifs' : '',                     
            'wl_mode' : 'sta',            'wl0_ssid' : ssid,                 'wl_ssid' :  ssid,                     
            'dns_redirect' : '1',         'dnsmasq_enable' : '0',            'wan_ipaddr_buf' : '192.168.33.10',          
          }
    from_db = [ 'sta_ifname','wl0_hw_rxchain','wl0_hw_txchain','wan_hwaddr' ]
    deletes = [ 'wl0_wpa_psk' ]
    ddwrt_program_mode( cn, pgm, from_db, deletes )

def ddwrt_learn( ddwrt_name, ddwrt_address, ddwrt_password, ddwrt_file ):
    global router_db
    cn = ddwrt_establish_connection( ddwrt_address, "root", ddwrt_password, b'#EOT#' )
    ddwrt_info = { }
    et0macaddr = ddwrt_get_single_line_result( cn, "nvram get et0macaddr" )
    for term in ( 'sta_ifname', 'wan_hwaddr', 'wl0_mode', 'wl0_hw_txchain', 'wl0_hw_rxchain' ):
        result = ddwrt_get_single_line_result( cn, "nvram get "+term )
        ddwrt_info[term] = result

    if ddwrt_name in router_db:
        old_info = router_db[ ddwrt_name ]
        if old_info[ 'et0macaddr' ] != et0macaddr:
            print( 'Name ' + ddwrt_name + ' is already used for another device: ' + old_info[ 'et0macaddr' ] )
            print( 'Choose a different name and try again.' )
            sys.exit()
        print( "updating info for " + ddwrt_name )
        old_info[ ddwrt_info[ 'wl0_mode' ] ] = ddwrt_info
        router_db[ ddwrt_name ] = old_info
    else:
        router_db[ ddwrt_name ] = { "name" : ddwrt_name, "address" : ddwrt_address, "password" : ddwrt_password ,
                                    "et0macaddr" : et0macaddr, ddwrt_info[ "wl0_mode" ] : ddwrt_info  }
    router_db[ ddwrt_name ][ 'InsertTime' ] = time.time()
    write_json_file( ddwrt_file, router_db )
    print( ddwrt_info[ 'wl0_mode' ] + ' mode learned' )
    if 'ap' not in router_db[ ddwrt_name ]:
        print( 'ap mode has not been detected yet for this ddwrt device. To use it for verification step, configure ap mode and re-learn' )
    elif 'sta' not in router_db[ ddwrt_name ]:
        print( 'sta mode has not been detected yet for this ddwrt device. To use it for configuration step, configure client mode with static wan address 192.168.33.10 and re-learn' )
    else:
        print( 'Device is now fully learned, ready for configuration and verification of target' )

def ddwrt_choose_roles( ddwrt_name ):
    nodes = []
    ap_node = 0
    sta_node = len( ddwrt_name ) - 1
    for node in ddwrt_name:
        nodes.append( ddwrt_connect_to_known_router( node ) )
    ap_capable = []
    sta_capable = []
    current_ap = []
    current_sta = []
    for i in range( len(nodes) ):
        if 'ap' in nodes[i]['router']: ap_capable.append( i )
        if 'sta' in nodes[i]['router']: sta_capable.append( i )
        if 'ap' == nodes[i]['current_mode']: current_ap.append( i )
        if 'sta' == nodes[i]['current_mode']: current_sta.append( i )
    if len( ap_capable ) == 0:
        print( "No AP capable dd-wrt device found. Re-learn the device with it set in AP mode" )
        sys.exit()
    if len( sta_capable ) == 0:
        print( "No client-mode capable dd-wrt device found. Re-learn the device with it set in client mode" )
        sys.exit()
    if len( nodes ) > 1:
        if len( ap_capable ) < 2:
            ap_node = ap_capable[0]
            sta_node = ( ap_node + 1 ) % 2
        elif len( sta_capable ) < 2:
            sta_node = sta_capable[0]
            ap_node = ( sta_node + 1 ) % 2
        elif len( current_ap ) < 2:
            ap_node = current_ap[0]
            sta_node = ( ap_node + 1 ) % 2
        elif len( current_sta ) < 2:
            sta_node = sta_capable[0]
            ap_node = ( sta_node + 1 ) % 2
    return( nodes[ ap_node ], nodes[ sta_node ] )

def ddwrt_discover( cn, prefix ):
    cmd = "site_survey 2>&1"
    ( result, err ) = ddwrt_do_cmd( cn['conn'], cmd, cn['eot'] )
    if not result and err != '':
        eprint( err )
        sys.exit( )
    ret = []
    for n in range( 1, len( result ) ):
        r = re.sub( r'.*SSID\[ *(.*)\] BSSID\[.*', r'\1', result[ n ] )
        if r.startswith( prefix ):
            ret.append( r )
    return ret

def ddwrt_wget( cn, url, verbose, msg, tries = 1 ):
    passes = 0
    if msg:
        sys.stdout.write( msg )
    if verbose > 0:
        print( url )
    while True:
        passes += 1
        if msg:
            sys.stdout.write( "." )
            sys.stdout.flush( )
        ( result, err ) = ddwrt_do_cmd( cn['conn'], "wget -T 1 -qO- '" + url + "'; echo", cn['eot'] )
        if ( len(result) > 1 or result[0] != '' ) or passes > tries:
            break
        time.sleep( 2 )
    if msg: print( )
    return ( result, err )

####################################################################################
#   Label interface
####################################################################################

def import_label_lib( print_using ):
    global labelprinting
    labelprinting = importlib.import_module( print_using )
    if 'make_label' not in dir( labelprinting ):
        print( "The module " + print_using + " does not contain a function 'make_label()'." )
        sys.exit( )

def print_label( dev_info ):
    try:
        labelprinting.make_label( dev_info )
    except:
        for i in range(3): print()
        print( "*******************************************" )
        print( "* Failure in custom label printing module *" )
        print( "*      stack trace follows...             *" )
        print( "*******************************************" )
        for i in range(3): print()
        raise

def test_print( ):
    dev_info = {
            "Group": "foo",
            "Label": "Las Vegas, NV. Store #45",
            "Origin": "provision-list",
            "SSID": "TestNet",
            "Password": "12xyzab34",
            "StaticIP": "192.168.1.22",
            "NetMask": "255.255.192.0",
            "factory_ssid": "shelly1-746290",
            "InProgressTime": 1625598429.713981,
            "CompletedTime": 1625598447.571315,
            "ConfirmedTime": 1625598447.6824908,
            "status": {
                "wifi_sta": {
                    "connected": False,
                    "ssid": "",
                    "ip": "192.168.33.1"
                },
                "mac": "ECFABC746290",
                "update": {
                    "status": "unknown",
                    "has_update": False,
                    "new_version": "",
                    "old_version": "20210429-100340/v1.10.4-g3f94cd7"
                }
            },
            "settings": {
                "device": {
                    "type": "SHSW-1",
                    "mac": "ECFABC746290",
                    "hostname": "shelly1-746290",
                    "num_outputs": 1
                },
                "wifi_ap": {
                    "enabled": False,
                    "ssid": "shelly1-746290",
                    "key": ""
                },
                "wifi_sta": {
                    "enabled": True,
                    "ssid": "TestNet",
                    "ipv4_method": "static",
                    "ip": "192.168.1.22",
                    "gw": None,
                    "mask": "255.255.192.0",
                    "dns": None
                },
                "fw": "20210429-100340/v1.10.4-g3f94cd7",
                "build_info": {
                    "build_id": "20210429-100340/v1.10.4-g3f94cd7",
                    "build_timestamp": "2021-04-29T10:03:40Z",
                    "build_version": "1.0"
                }
            }
        }
    print_label( dev_info )

####################################################################################
#   HTTP Utilities
####################################################################################

def url_encode( vals ):
    if type( vals ) == type( { } ):
        return urlencode( dict( [ [ v, vals[ v ] if vals[ v ] != None else '' ] for v in vals ] ) ).replace( 'urls%5B%5D', 'urls[]' )
    else:
        return urlencode( [ ( n, v ) if v != None else ( n, '' ) for ( n, v ) in vals ] ).replace( 'urls%5B%5D', 'urls[]' )

def get_url( addr, tm, verbose, url, operation, tmout = 2 ):
    for i in range( 5 ):
        contents=""
        raw_data=""
        if verbose and operation != '':
            print( 'Attempting to connect to device at ' + addr + ' ' + operation )
            if verbose > 1:
                print( url )
        try:
            raw_data = url_read( url, tmout = tmout )
            contents = json.loads( raw_data )
        except HTTPError as e:
            print('Error code:', e.code)
            print( e.read( ) )
        except BaseException as e:
            if verbose or i > 3: print( e )
       
        if contents:
            if verbose > 1:
                print( repr( contents ) )
            return contents
        time.sleep( tm )

    print( "Failed five times to contact device at " + addr + ". Try increasing --time-to-pause option, or move device closer" )
    if raw_data: print( "Raw results from last attempt: " + raw_data )
    return None

def set_settings_url( address, ssid, pw, static_ip, ip_mask, gateway ):
    if static_ip:
        gw = ( "&gateway=" + gateway ) if gateway else ''
        return "http://" + address + "/settings/sta/?enabled=1&ssid=" + urlquote(ssid) + "&key=" + urlquote(pw) + "&ipv4_method=static&ip=" + static_ip + "&netmask=" + ip_mask + gw
    else:
        return "http://" + address + "/settings/sta/?enabled=1&ssid=" + urlquote(ssid) + "&key=" + urlquote(pw) + "&ipv4_method=dhcp"

####################################################################################
#   JSON Utilities
####################################################################################

def read_json_file( f, empty, validate = False ):
    valid = True
    try:
        with open( f, 'r' ) as openfile:
            result = json.load( openfile )
            if validate:
                if type( empty ) != type( result ):
                    valid = False
                elif type( result ) == type( {} ):
                    if 'format' not in result or result[ 'format' ] != 'automagic':
                        valid = False
                elif type( result ) == type( [] ) and len( result ) >= 1:
                    valid = False
                    for v in validate:
                        if v in result[0]:
                            valid = True
            if not valid:
                print( "File " + f + " was not written by this program, or is corrupt." )
                sys.exit()
            return result
    except IOError as e:
        if empty == 'fail':
            print( e )
            sys.exit( )
        return empty

def write_json_file( f, j ):
    try:
        with open( f, "w" ) as outfile:
            outfile.write( json.dumps( j, indent = 4 ) )
    except IOError as e:
        print( e )
        sys.exit( )

####################################################################################
#   Shelly-specific HTTP logic
####################################################################################

def status_url( address ):
    return "http://" + address + "/status"

def get_settings_url( address, rec = None ):
    map = { "DeviceName" : "name", "LatLng" : "lat:lng", "TZ" : "tz_dst:tz_dst_auto:tz_utc_offset:tzautodetect" }
    parms = {}
    if rec:
         for tag in map:
             if tag in rec:
                 for elem in zip( map[ tag ].split(':'), rec[ tag ].split(':') ):
                     parms[ elem[ 0 ]  ] = elem[ 1 ]
    q = "?" + url_encode( parms ) if parms else ""
    return "http://" + address + "/settings" + q

def ota_url( addr, fw ):
    if fw == 'LATEST':
        return "http://" + addr + "/ota?update=1"
    return "http://" + addr + "/ota?url=" + fw

def get_status( addr, tm, verbose ):
    url = status_url( addr )
    return get_url( addr, tm, verbose, url, 'to confirm status' )

def get_actions( addr, tm, verbose ):
    url = "http://" + addr + "/settings/actions"
    return get_url( addr, tm, verbose, url, 'to read actions' )

def get_toggle_url( ip, dev_type ):
    ### return "http://" + ip + "/" + dev_type + "/0?turn=on&timer=1"
    return "http://" + ip + "/" + dev_type + "/0?turn=toggle"

def toggle_device( ip_address, dev_type ):
    success_cnt = 0
    fail_cnt = 0
    use_type = None
    while True:
        result1 = '' 
        result2 = ''
        # TODO: use dev_type to determine relay/light. For now, try both.
        if not use_type or use_type == 'light':
            try:
                result2 = url_read( get_toggle_url( ip_address, 'light' ) )
            except:
                result2 = ""
            if not use_type and result2 != '': use_type = 'light'
        if not use_type or use_type == 'relay':
            try:
                result1 = url_read( get_toggle_url( ip_address, 'relay' ) )
            except:
                result1 = ""
            if not use_type and result1 != '': use_type = 'relay'
        if result1 != '' or result2 != '':
            success_cnt += 1
            fail_cnt = 0
        else:
            fail_cnt += 1
        time.sleep( 0.5 )
        if success_cnt > 0 and fail_cnt > 1 or fail_cnt > 5: break

    if success_cnt == 0:
        print( "Unsuccessful attempt to toggle device." )

def ota_flash( addr, tm, fw, verbose, dry_run ):
    url = ota_url( addr, fw )
    if dry_run:
        print( url )
        return False
    return get_url( addr, tm, verbose, url, 'to flash firmware' )

def find_device( dev ):
    try:
        attempt = url_read( 'http://' + dev[ 'IP' ] + '/ota', tmout = 0.5 )
    except:
        attempt = None
    if attempt: return True
    return False

####################################################################################
#   Output Utilities
####################################################################################

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def fail_msg( s ):
    for i in range(3): print( )
    print( s )
    for i in range(3): print( )

####################################################################################
#   Library Functions
####################################################################################

def check_for_device_queue( dq, group = None, include_complete = False ):
    txt = "Use import to specify some provisioning instructions."
    if len( dq ) == 0:
        print( "List is empty. " + txt )
        sys.exit()
    for rec in dq:
        if ( include_complete or 'CompletedTime' not in rec ) and ( not group or 'Group' in rec and rec[ 'Group' ] == group ):
            return
    if group:
        print( "Group " + group + " has no list entries ready to provision. " + txt )
    else:
        print( "List has no entries ready to provision. " + txt )
    sys.exit()

def short_heading( c ):
    return c if re.search( '\.[0-9]+\.', c ) else re.sub( '.*\.', '', c )

def get_name_value_pairs( query_conditions, term_type = '--query-condition' ):
    result = [ x.split('=') for x in query_conditions.split(',') ] if query_conditions else []
    for q in result:
        if len(q) < 2:
            print( "Each " + term_type + " term must contain name=value" )
            sys.exit()
    return result

def complete_probe( args, rec, initial_status = None ):
    global device_db

    ip_address = rec[ 'ProbeIP' ]
    if not args.refresh or args.operation == 'probe-list': eprint( ip_address )
    if not initial_status:
        initial_status = get_url( ip_address, args.pause_time, args.verbose, status_url( ip_address ), 'to get current status' )
    if initial_status:
        if args.verbose > 1:
            print( ip_address )
        configured_settings = get_url( ip_address, args.pause_time, args.verbose, get_settings_url( ip_address ), 'to get config' )
        actions = get_actions( ip_address, 1, args.verbose )
        if actions and 'actions' in actions:
            rec['actions'] = actions[ 'actions' ]
        id = initial_status['mac']
        if id in device_db:
            rec.update( device_db[ id ] )
        else:
            rec['ProbeTime'] = time.time()
        rec['UpdateTime'] = time.time()
        rec['status'] = initial_status
        if configured_settings:
            rec['settings'] = configured_settings
            rec['CompletedTime'] = time.time()
        else:
            print( "Failed to update settings for " + id )
        rec['Origin'] = 'probe-list'
        rec['IP'] = ip_address
        rec['ID'] = id
        device_db[ id ] = rec

def import_json( file, queue_file ):
    list = read_json_file( file, 'fail' )
    append_list( list )
    write_json_file( queue_file, device_queue )

def import_csv( file, queue_file ):
    with open( file ) as csvfile:
       reader = csv.DictReader( csvfile )
       append_list( reader )
    write_json_file( queue_file, device_queue )

def finish_up_device( device, rec, operation, args, new_version, initial_status, configured_settings = None ):
    global device_db
    rec[ 'ConfirmedTime' ] = time.time()
    #need_update = False

    if not configured_settings: configured_settings = get_url( device, args.pause_time, args.verbose, get_settings_url( device, rec ), 'to get config' )
    rec[ 'status' ] = initial_status
    rec[ 'settings' ] = configured_settings if configured_settings else {}
    rec[ 'Origin' ] = operation
    print( "in finish_up_device: " + repr( initial_status ) )
    rec[ 'ID' ] = initial_status[ 'mac' ]
    rec[ 'IP' ] = initial_status[ 'wifi_sta' ][ 'ip' ]
    device_db[ initial_status[ 'mac' ] ] = rec
    write_json_file( args.device_db, device_db )

    #if 'DeviceName' in rec:
    #    new_settings = get_url( device, args.pause_time, args.verbose, get_settings_url( device, rec ), 'to set device name' )
    #    need_update = True
    #    rec['settings'] = new_settings

    if args.ota != '':
        if flash_device( device, args.pause_time, args.verbose, args.ota, args.ota_timeout, new_version, args.dry_run ):
    #        need_update = True
            new_status = get_status( device, args.pause_time, args.verbose )
            rec['status'] = new_status if new_status else {}
    #if need_update:
            device_db[ initial_status['mac'] ] = rec
            write_json_file( args.device_db, device_db )

    if args.print_using: 
        print_label( rec )

    if args.toggle:
        try:
            print( "Toggling power on newly provisioned device. Unplug to continue." )
            toggle_device( device, configured_settings['device']['type'] )
        except KeyboardInterrupt as error:
            print( )
            print( )

####################################################################################
#   Query/db functions
####################################################################################

def flatten( d, prefix='', devtype = None ):
    result = { }
    guide = { }
    if not devtype and type(d) == type({}):
        devtype = d['settings']['device']['type'] if 'settings' in d and 'device' in d['settings'] and 'type' in d['settings']['device'] else None
    if type( d ) == type( { } ):
        for k in d:
            new_data = {}
            new_guide = {}
            if type( d[k] ) == type( {} ):
                ( new_data, new_guide ) = flatten( d[k], prefix + k + '.', devtype )
            elif type( d[k] ) == type( [] ):
                for i in range(len(d[k])):
                    ( tmp_data, tmp_guide ) = flatten( d[k][i], prefix + k + '.' + str(i) + '.', devtype )
                    new_data.update( tmp_data )
                    new_guide.update( tmp_guide )
            else:
                new_data[ k ] = str( d[k] )
                new_data[ prefix + k ] = str( d[k] )
                pk = re.sub( '\.[0-9]+\.', '.[n].', prefix + k )
                if k not in new_guide: new_guide[ k ] = { }
                new_guide[ k ][ devtype ] = pk
                if prefix + k not in new_guide: new_guide[ prefix + k ] = { }
                new_guide[ prefix + k ][ devtype ] = pk
            new_data.update( result )       # Give first/original key priority
            result = new_data               # and replace result for next iteration
            guide = deep_update( new_guide, guide )
    else:
        guide = {}
        pk = re.sub( '\.[0-9]+\.', '.[n].', prefix )
        pk = re.sub( '\.$', '', pk )
        prefix = re.sub( '\.$', '', prefix )
        if prefix not in guide: guide[ prefix ] = { }
        guide[ prefix ][ devtype ] = pk
        result = { prefix : str( d ) }
    return [ result, guide ]

def match_rec( rec, query_conditions, match_tag, group, restore_device, access ):
    for q in query_conditions:
        if q[0] not in rec or rec[q[0]] != q[1]:
            return False
    if match_tag and ( 'Tags' not in rec or match_tag not in rec['Tags'].split(',') ):
        return False
    if group and ( not 'Group' in rec or rec[ 'Group' ] != group ):
        return False
    if restore_device and restore_device != 'ALL' and restore_device != rec[ 'ID' ]:
        return False
    if access != 'ALL':
        presumed = 'Continuous' if 'Access' not in rec else rec[ 'Access' ]
        if presumed != access:
            return False
    return True

def schema_details( col, coverage, verbosity ):
    paths = {}
    for devtype in coverage:
        if coverage[devtype] not in paths:
            paths[ coverage[devtype] ] = []
        paths[coverage[devtype]].append( devtype )
    if verbosity > 1:
        return [ col, paths ]
    elif verbosity > 0:
        if len(paths) > 1 or list(paths.keys())[0] != re.sub('\.[0-9]+\.','.[n].',col):
            return [ col, paths ]
        else:
            return [ col ]
    else:
        return [ col ]

def print_details( col, paths, verbosity, max_width ):
    if verbosity > 1 and paths:
        print( col + ':' )
        for p in paths:
            #print(repr(p))
            #print(repr(paths))
            ###print( '    ' + p  + ' [ '+  ', '.join( paths[ p ] ) + ' ]' )
            print( '    ' + p  + ' [ '+  ', '.join( [ x for x in paths[ p ] if x ] ) + ' ]' )
    elif verbosity > 0 and paths:
        print( col.ljust( max_width ) + ': ' + ', '.join( p for p in paths ) )
    else:
        print( col )

####################################################################################
#   Operations
####################################################################################

def flash_device( addr, pause_time, verbose, ota, ota_timeout, new_version, dry_run ):
    print( "Checking old firmware version" )
    url = "http://" + addr + "/ota"
    result = get_url( addr, pause_time, verbose, url, 'to get current version' )
    if not result:
        print( "Could not get current firmware version for device " + addr )
        return False
    print( "status: " + result['status'] + ", version: " + result['old_version'] )
    if result['old_version'] == new_version:
        print( "Device is already up-to-date" )
        return True
    if result['status'] == 'updating':
        print( 'Error: Device already shows "updating"' )
        return False
    if ota_flash( addr, pause_time, ota, verbose, dry_run ):
        print( "Sent OTA instructions to " + addr )
        print( "New Version: " + repr( new_version ) )
        if ota_timeout == 0: return True
        print( "Pausing to wait to check for successful OTA flash..." )
        start_time = time.time( )
        seen_updating = False
        passes = 0
        while time.time( ) < start_time + ota_timeout:
            passes += 1
            time.sleep( pause_time )
            new_result = get_url( addr, pause_time, verbose, url, '' )
            if not new_result: return False
            if new_result['status'] == 'updating': 
                if seen_updating:
                    print( '.', end='' )
                    sys.stdout.flush( )
                else:
                    print( "status: " + new_result['status'] + ", version: " + new_result['old_version'] )
                seen_updating = True
            elif seen_updating:
                if not new_version or result['old_version'] != new_result['old_version']:
                    if not new_version or new_result['old_version'] == new_version:
                        print( "" )
                        print( "Success. Device " + addr + " updated from " + result['old_version'] + ' to ' + new_result['old_version'] )
                        return True
                    else:
                        print(repr(new_version))
                        fail_msg( "****possible OTA failure***  Device " + addr + ' still has unexpected build, not matching manifest: ' + new_result['old_version'] )
                        return False
                else:
                    break
            else:
                if passes > 10:
                    print( 'The device ' + addr + ' has never shown status "updating". Is it already on the version requested? ' )
                    return False
                print( "status: " + new_result['status'] + ", version: " + new_result['old_version'] )
        fail_msg( "****possible OTA failure***  Device " + addr + ' still has ' + new_result['old_version'] )
        return False

    else:
        if not dry_run: print( "Could not flash firmware to device " + addr )
        return False
    return True

def schema( args ):
    query_columns = args.query_columns.split(',') if args.query_columns else []
    query_conditions = get_name_value_pairs( args.query_conditions )
    u = {}
    guide = {}

    if args.refresh: probe_list( args )

    for d in device_db:
        if d == 'format':
            continue
        ( data, new_guide ) = flatten( device_db[ d ] )
        if match_rec( data, query_conditions, args.match_tag, args.group, None, args.access ):
            u.update( data )
            guide = deep_update( new_guide, guide )
    k = sorted( u.keys() )
    max_width = 0
    for s in k:
        if len(s) > max_width:
            max_width = len(s)
    results = []
    for s in k:
        if len( query_columns ) > 0:
            for q in query_columns:
                if q.split( '.' )[-1] in s.split( '.' ) and q in s:
                    results.append( schema_details( s, guide[ s ], args.verbose ) )
        else:
            results.append( schema_details( s, guide[ s ], args.verbose ) )

    for z in ( None, 'settings.', 'status.', '' ):
        for s in results:
            path = list(s[1].keys())[0] if len(s) > 1 else None
            if not z and z != '' and not path  \
                or z and z != '' and path and path.startswith(z) \
                or z and z == '' and path and not ( path.startswith('settings.') or path.startswith('status.') ):
                   print_details( s[0], s[1] if len(s) > 1 else None, args.verbose, max_width )

def apply( args, new_version, data, need_write ):
    configured_settings = None

    if args.ota != '':
        flash_device( data[ 'IP' ], args.pause_time, args.verbose, args.ota, args.ota_timeout, new_version, args.dry_run )

    if args.apply_urls:
        for url in args.apply_urls:
            if args.dry_run:
                print( 'http://' + data[ 'IP' ] + url )
            else:
                got = get_url( data[ 'IP' ], args.pause_time, args.verbose, 'http://' + data[ 'IP' ] + url, 'to apply ' + url )
                if not args.settings:
                    configured_settings = get_url( data[ 'IP' ], args.pause_time, args.verbose, get_settings_url( data[ 'IP' ] ), 'to get config' )
                    need_write = True

    if args.settings:
        new_settings = dict( get_name_value_pairs( args.settings, term_type = '--settings' ) )
        if args.dry_run:
            print( get_settings_url( data[ 'IP' ], new_settings ) )
        else:
            # apply_urls (above) depends on this, if both are used (to save time):
            configured_settings = get_url( data[ 'IP' ], args.pause_time, args.verbose, get_settings_url( data[ 'IP' ], new_settings ), 'to get config' )
            need_write = True

    if args.delete_device and ( args.delete_device == 'ALL' or args.delete_device == data[ 'ID' ] ):
        del device_db[ data[ 'ID' ] ]
        need_write = True

    if args.restore_device and ( args.restore_device == 'ALL' or args.restore_device == data[ 'ID' ] ):
        settings = device_db[ data[ 'ID' ] ][ 'settings' ]
        http_args = {}
        apply_list = []

        for s in settings:
            fields = settings[ s ]
            if type( fields ) == type( {} ):
                if s in exclude_setting: continue
                s = re.sub( '^wifi_', '', s )
                if s == 'sntp':
                    apply_list.append( 'http://' + data[ 'IP' ] + '/settings/?' + url_encode( { 'sntp_server' : '' if fields['enabled'] == 'false' else fields[ 'server' ] } ) )
                elif s == 'mqtt':
                    flds = dict( [ [ 'mqtt_' + f, fields[ f ] ] for f in fields ] )
                    apply_list.append( 'http://' + data[ 'IP' ] + '/settings/?' + url_encode( flds ) )
                elif s == 'coiot':
                    flds = dict( [ [ 'coiot_' + f, fields[ f ] ] for f in fields ] )
                    apply_list.append( 'http://' + data[ 'IP' ] + '/settings/?' + url_encode( flds ) )
                else:
                    apply_list.append( 'http://' + data[ 'IP' ] + '/settings/' + s + '?' + url_encode( fields ) )
            elif type( fields ) == type( [] ):
                if s in exclude_setting: continue
                name = re.sub( 's$', '', s )
                for i in range( len( fields ) ):
                    channel = fields[ i ]
                    if type( channel ) == type( {} ):
                        flds = dict( [ [ f, channel[ f ] ] for f in channel if f not in exclude_setting ] )
                        apply_list.append( 'http://' + data[ 'IP' ] + '/settings/' + name + '/' + str( i ) + '/?' + url_encode( flds ) )
                        if 'schedule' in channel and 'schedule_rules' in channel:
                             rules = ','.join( channel[ 'schedule_rules' ] )
                             apply_list.append( 'http://' + data[ 'IP' ] + '/settings/' + name + '/' + str( i ) + '/?' + \
                                url_encode( { 'schedule' : channel[ 'schedule' ], 'schedule_rules': rules } ).replace("schedule_rules=%5B%5D","").replace("%5B","[").replace("%5D","]" ) )
                    ### else:  'alt_modes' : 'white' ???
            elif s not in exclude_setting:
                http_args[ s ] = fields

        apply_list.append( 'http://' + data[ 'IP' ] + '/settings?' + url_encode( http_args ) )
                
        if 'actions' in device_db[ data[ 'ID' ] ]:
            actions = device_db[ data[ 'ID' ] ][ 'actions' ]
            for a in actions:
                for u in actions[ a ]:
                    ### btn_on_url: [{u'index': 0, u'enabled': True, u'urls': [u'http://192.168.1.254/zzzfoo']}]
                    http_args = [ ( 'urls[]', x ) for x in u[ 'urls' ] ]
                    http_args.append( ( 'name', a ) )
                    for p in u:
                        if p != 'urls':
                            http_args.append( ( p, u[ p ] ) )
                    apply_list.append( 'http://' + data[ 'IP' ] + '/settings/actions?' + url_encode( http_args ) )

        if args.dry_run:
             for u in apply_list:
                   print(u)
             print( )
        else:
             for u in apply_list:
                 got = get_url( data[ 'IP' ], args.pause_time, args.verbose, u, None)
                 if not got:
                     print( "could not apply " + u )
                 time.sleep( .1 )
                 sys.stdout.write( "." )
                 sys.stdout.flush()
             print( )
             configured_settings = get_url( data[ 'IP' ], args.pause_time, args.verbose, get_settings_url( data[ 'IP' ] ), 'to get config' )
             need_write = 1

    return( configured_settings, need_write )

def query( args, new_version = None ):
    global device_db
    need_write = False
    results = [ ]

    if args.refresh: probe_list( args )

    if args.query_columns and args.query_columns.startswith('+'):
        query_columns = default_query_columns
        query_columns.extend( re.sub('^\+','',args.query_columns).split(',') )
    else:
        query_columns = args.query_columns.split(',') if args.query_columns else default_query_columns

    delete_list = [ q.replace("-","") for q in query_columns if q.startswith("-") ]
    query_columns = [ q for q in query_columns if q not in delete_list and not q.startswith("-") ]

    query_conditions = get_name_value_pairs( args.query_conditions )

    guide = {}
    tmp = []
    for d in device_db:
        if d == 'format':
            continue
        ( data, new_guide ) = flatten( device_db[ d ] )
        guide.update( new_guide )
        tmp.append( data )

    column_map = {}
    for q in query_columns:
        if q not in guide:
            for g in guide:
                if g.endswith( "." + q ):
                     column_map[ q ] = g

    query_columns = [ column_map[ q ] if q in column_map else q for q in query_columns ]

    column_widths = { }
    for data in tmp:
        res = { }
        for c in query_columns:
            hc = c if args.verbose > 0 else short_heading( c ) 
            res[ c ] = data[ c ] if c in data else ""
            if hc not in column_widths: column_widths[ hc ] = len( hc )
            column_widths[ hc ] = len( res[ c ] ) if len( res[ c ] ) > column_widths[ hc ] else column_widths[ hc ]
        results.append( [ res, data ] )

    res = ""
    dashes = ""
    for c in query_columns:
        hc = c if args.verbose > 0 else short_heading( c )
        res = res + hc.ljust( column_widths[ hc ]+1 )
        dashes = dashes + ( "-" * column_widths[ hc ] ) + " "
    print( res )
    print( dashes )

    k = list( results[0][0].keys( ) )[0]
    results.sort( key=lambda x: x[0][k], reverse=False )
    todo = []
    nogo = []
    continuous_count = 0
    total_count = 0
    for ( res, data ) in results:
        if match_rec( data, query_conditions, args.match_tag, args.group, args.restore_device, args.access ):
            if args.set_tag or args.delete_tag:
                need_write = True
                old_tags = data['Tags'].split(',') if 'Tags' in data and data['Tags'] != '' else []
                if args.set_tag:
                    data[ 'Tags' ] = ','.join( set( old_tags ).union( [ args.set_tag ] ) )
                if args.delete_tag:
                    data[ 'Tags' ] = ','.join( set( old_tags ).difference( [ args.delete_tag ] ) )
                device_db[ data[ 'ID' ] ][ 'Tags' ] = data[ 'Tags' ]
            result = ""
            for c in query_columns:
                hc = c if args.verbose > 0 else short_heading( c )
                result += res[ c ].ljust( column_widths[ hc ]+1 )

            if 'IP' not in data:
                nogo.append( [ result, res, data ] )
            else:
                if 'Access' not in data or data[ 'Access' ] == 'Continuous':
                    continuous_count += 1
                todo.append( [ result, res, data ] )
                total_count += 1

    for (result, res, data) in todo:
         print( result )

    if args.operation == 'apply':
        print( )
        if nogo:
            print( "These devices have no stored IP. No changes will be applied." )
            for (result, res, data) in nogo:
                print( data[ 'ID' ] )
            print( )

        if todo and not args.dry_run:
            print( "Applying changes..." )

        done = []
        passes = 0
        while( todo ):
            passes += 1
            for ( result, res, data ) in todo:
                if find_device( data ):
                    done.append( [ result, res, data ] )
                    if not args.dry_run: print( data[ 'IP' ] )
                    ( configured_settings, need_write ) = apply( args, new_version, data, need_write )
                    total_count -= 1
                    if 'Access' not in data or data[ 'Access' ] == 'Continuous':
                        continuous_count -= 1
                        
                        if continuous_count == 0 and total_count > 0:
                           print( )
                           print( "Only Periodic WiFi-connected devices remain. Polling until they are found..." )

            todo = [ r for r in todo if r not in done ]

            if passes > 10 and continuous_count == total_count:
                 print( )
                 print( "These device could not be contacted:" )
                 for ( result, res, data ) in todo:
                    print( data[ 'IP' ] )
                 break

            if todo:
                time.sleep(.5)

        if configured_settings:
            device_db[ data[ 'ID' ] ][ 'settings' ] = configured_settings

    if need_write:
        write_json_file( args.device_db, device_db )

def probe_list( args ):
    query_conditions = [ x.split('=') for x in args.query_conditions.split(',') ] if args.query_conditions else []
    if args.refresh:
        dq = [ device_db[ k ] for k in device_db.keys() if 'ProbeIP' in device_db[ k ] ]
    else:
        dq = device_queue

    todo = []
    for rec in dq:
        if match_rec( rec, query_conditions, args.match_tag, args.group, None, args.access ) and 'ProbeIP' in rec: 
            todo.append( rec )

    if not args.refresh:
        check_for_device_queue( todo, args.group, True )

    if args.refresh and args.operation != 'probe-list':
        eprint( "Refreshing info from network devices" )

    done = []
    probe_count = 1
    need_write = False
    # todo: Look for Periodic-type devices in queue and message that it might take a while
    while len( todo ):
        #sys.stdout.write( "." )
        #sys.stdout.flush()
        for rec in todo:
            if need_write and ( probe_count % 10 == 0 or 'Access' in rec and rec[ 'Access' ] == 'Periodic' ):
                write_json_file( args.device_db, device_db )
            initial_status = None
            try:
                initial_status = json.loads( url_read( status_url( rec[ 'ProbeIP' ] ), tmout = 0.5 ) )
                break
            except:
                pass
        if initial_status:
            done.append( rec )
            complete_probe( args, rec, initial_status )
            need_write = True
            probe_count += 1
        time.sleep( 0.5 )
        todo = [ r for r in todo if r not in done ]

    if need_write:
        write_json_file( args.device_db, device_db )

def provision_list( args, new_version ):
    global device_queue, device_db
    t1 = timeit.default_timer()
    check_for_device_queue( device_queue, args.group )
    ( ap_node, sta_node ) = ddwrt_choose_roles( args.ddwrt_name )
    if args.timing: print( 'setup time: ', round( timeit.default_timer() - t1, 2 ) )
    setup_count = 0
    success_count = 0
    for rec in device_queue:
        if 'CompletedTime' in rec or args.group and ( not 'Group' in rec or rec[ 'Group' ] != args.group ):
            continue
        if 'SSID' not in rec:
            continue
        if setup_count > 0 and args.cue:
            print()
            print()
            getpass.getpass( "Press <enter> to continue" )
        setup_count += 1
        sys.stdout.write( "Waiting to discover a new device" )
        while True:
            sys.stdout.write( "." )
            sys.stdout.flush()
            t1 = timeit.default_timer()
            device_ssids = ddwrt_discover( sta_node, args.prefix )
            if len( device_ssids ) > 0:
                if args.timing: print( 'discover time: ', round( timeit.default_timer() - t1, 2 ) )
                print( "" )
                print( "Ready to program " + device_ssids[0] + " with " + repr( rec ) )
                rec[ 'factory_ssid' ] = device_ssids[0]
                rec[ 'InProgressTime' ] = time.time()
                write_json_file( args.device_queue, device_queue )

                attempts = 0
                while True:
                    attempts += 1
                    # With different ddwrt devices, faster to pre-configure AP
                    t1 = timeit.default_timer()
                    if ap_node[ 'router' ][ 'et0macaddr' ] != sta_node[ 'router' ][ 'et0macaddr' ]:
                        ddwrt_set_ap_mode( ap_node, rec[ 'SSID' ], rec[ 'Password' ] )

                    ddwrt_set_sta_mode( sta_node, device_ssids[0] )
                    if args.timing: print( 'dd-wrt device configuration time: ', round( timeit.default_timer() - t1, 2 ) )

                    t1 = timeit.default_timer()
                    ( response, err ) = ddwrt_wget( sta_node, status_url( factory_device_addr ), args.verbose, None, 10 )
                    if args.timing: print( 'initial status time: ', round( timeit.default_timer() - t1, 2 ) )
                    initial_status = json.loads( response[0] )

                    t1 = timeit.default_timer()
                    if 'StaticIP' in rec:
                        url = set_settings_url( factory_device_addr, rec[ 'SSID' ], rec[ 'Password' ], rec[ 'StaticIP'], rec[ 'NetMask' ], rec[ 'Gateway' ] )
                    else:
                        url = set_settings_url( factory_device_addr, rec[ 'SSID' ], rec[ 'Password' ], None, None, None )
                    ( result, err ) = ddwrt_wget( sta_node, url, args.verbose, None, 5 )
                    ###LOG### print( result )
                    if args.timing: print( 'settings time: ', round( timeit.default_timer() - t1, 2 ) )

                    # wait for site_survey to drop the device
                    passes = 0
                    misses = 0
                    sys.stdout.write( "Waiting for device SSID to drop from WiFi survey" )
                    t1 = timeit.default_timer()
                    while misses < 3 and passes < 60:
                        time.sleep( 1 )
                        passes += 1
                        check_ssids = ddwrt_discover( ap_node, args.prefix )
                        if device_ssids[ 0 ] in check_ssids:
                            misses = 0
                            sys.stdout.write( "." )
                        else:
                            misses += 1
                            sys.stdout.write( "+" )
                        sys.stdout.flush()
                    if args.timing: print( 'WiFi drop wait time: ', round( timeit.default_timer() - t1, 2 ) )

                    print( "" )
                    if misses >= 3: 
                        break

                    if attempts >= 10:
                        print( "Device failed to take AP programming instructions after 10 attemps." )
                        sys.exit( )
                    else:
                        print( "Device failed to take AP programming instructions. Trying again." )

                # If just one ddwrt device, then switch from sta back to AP now
                if ap_node[ 'router' ][ 'et0macaddr' ] == sta_node[ 'router' ][ 'et0macaddr' ]:
                    t1 = timeit.default_timer()
                    ddwrt_set_ap_mode( ap_node, rec[ 'SSID' ], rec[ 'Password' ] )
                    if args.timing: print( 'dd-wrt device reconfig time: ', round( timeit.default_timer() - t1, 2 ) )

                t1 = timeit.default_timer()
                if 'StaticIP' in rec:
                    ip_address = rec[ 'StaticIP' ]
                else:
                    ip_address = device_ssids[ 0 ]

                rec[ 'CompletedTime' ] = time.time()

                msg = "Finding " + ip_address + " on new network"
                ( response, err ) = ddwrt_wget( ap_node, get_settings_url( ip_address, rec ), args.verbose, msg, 40 )
                configured_settings = json.loads(response[0])

                if args.timing: print( 'WiFi transition time:', round( timeit.default_timer() - t1, 2 ) )

                if configured_settings == '':
                    print( "Failed to find device on network" )
                    sys.exit()

                success_count += 1
                write_json_file( args.device_queue, device_queue )

                if args.verbose > 1: print( repr( configured_settings ) )
                print( )

                new_status = get_status( ip_address, args.pause_time, args.verbose )
                finish_up_device( ip_address, rec, 'provision-list', args, new_version, new_status, configured_settings )
                break
            else:
                ## print( 'Found no new devices. Waiting ' + str(args.wait_time) + ' seconds before looking again. Press ^C to cancel' )
                time.sleep( args.wait_time )
    print( "Successfully provisioned " + str( success_count ) + " out of " + str( setup_count ) + " devices." )

def append_list( l ):
    global device_queue
    n = 0
    for row in l:
        n += 1
        r = {}
        for k in required_keys:
            if k not in row and 'ProbeIP' not in row:
                print( 'Required key ' + k + ' missing at record ' + str( n ) + ' of import file' )
                print( repr( row ) )
                sys.exit()
            if k in row:
                r[ k ] = row[ k ]
        for k in optional_keys:
            if k in row:
                if k == 'StaticIP' and row[ k ]:
                    r[ 'IP' ] = row[ 'StaticIP' ]
                    if 'NetMask' not in row or not row[ 'NetMask' ]:
                        print( "Record " + str( n ) + " contains StaticIP but not NetMask. Correct the import file to supply both." )
                        sys.exit( )
                if k == 'LatLng' and row[ k ]:
                    if not re.match('^[+-]?([0-9]+([.][0-9]*)?|[.][0-9]+):[+-]?([0-9]+([.][0-9]*)?|[.][0-9]+)$',row[ k ]):
                        print( "Record " + str( n ) + " contains improper LatLng. Must be of the form lat:lng" )
                        sys.exit( )
                if k == 'TZ' and row[ k ]:
                    if not re.match('^(True|False):(True|False):[+-]?([0-9]+):(True|False)$',row[ k ]):
                        print( "Record " + str( n ) + " contains improper TZ. Must be of the form tz_dst:tz_dst_auto:tz_utc_offset:tzautodetect" )
                        sys.exit( )

                if k == 'Access' and row[ k ]:
                    if row[ k ] not in ( 'Continuous', 'Periodic' ):
                        print( "Record " + str( n ) + " contains improper Access value. Must be one of Continuous or Periodic" )
                        sys.exit( )

                r[ k ] = row[ k ]
        r[ 'InsertTime' ] = time.time()
        device_queue.append( r )

def print_list( queue_file, group ):
    check_for_device_queue( device_queue, group )

    print( "List of devices for probe-list or provision-list operation" )
    header = [ 'ProbeIP', 'Group', 'SSID', 'Password', 'StaticIP', 'NetMask', 'Gateway', 'DeviceName', 'InsertTime' ]
    col_widths = [ 0 ] * len(header)
    result = [ header, [] ]
    for d in device_queue:
        if 'Group' in d and d['Group'] == group or not group:
            rec = []
            for h in header:
                rec.append( d[h] if h in d else '' )
            result.append( rec )
            for i in range( len( header ) ):
                if len( str( rec[i] ) ) > col_widths[i]:
                    col_widths[i] = len( str( rec[i] ) )
    for i in range(len(header)):
        if col_widths[i] > 0 and col_widths[i] < len(header[i]):
            col_widths[i] = len(header[i])
    for rec in result:
        pr = ""
        if len(rec):
            for v in zip( rec, col_widths ):
                 if v[1] > 0:
                     pr += str( v[0] ).ljust( v[1] + 1 )
        else:
            for i in range(len(header)):
                 if col_widths[i] > 0:
                     pr += "-" * col_widths[i] + " "
        print( pr )

def clear_list( queue_file ):
    write_json_file( queue_file, [] )

def provision( credentials, args, new_version ):
    prior_ssids = {}
    ssid = credentials['ssid']
    pw = credentials['password']
    setup_count = 0

    settings = get_name_value_pairs( args.settings, term_type = '--settings' )

    if args.ssid and args.ssid != ssid:
        print('Connect to ' + args.ssid + ' first')
        sys.exit()

    if not args.ssid:
        print( "Found current SSID " + ssid + ". Please be sure this is a 2.4GHz network before proceeding." )
        answer = input( 'Connect devices to SSID ' + ssid + '? (Y/N)> ' )
        if answer.upper() not in ('Y','YES'):
            print('Connect to desired SSID first')
            sys.exit()

    init()
    while True:
        if setup_count > 0 and args.cue:
            print()
            print()
            getpass.getpass( "Press <enter> to continue" )
        init()
        found = connect( credentials, args.prefix, prefix=True, ignore_ssids=prior_ssids, verbose=args.verbose )
        if found:
            rec = { }
            rec[ 'InProgressTime' ] = time.time()

            print( "Found: " + found )
            prior_ssids[ found ] = 1
            time.sleep( args.pause_time )
            if not get_status( factory_device_addr, args.pause_time, args.verbose ):
                if not reconnect( credentials ):
                    print( "Could not reconnect to " + ssid )
                break

            got_one = False
            setup_count += 1
            for i in range(5):
                time.sleep( args.pause_time )
                # Load the URL three times, even if we are successful the first time
                for j in range(3):
                    try:
                        req=set_settings_url( factory_device_addr, ssid, pw, None, None, None )
                        content = json.loads( url_read( req ) )
                        if args.verbose > 1:
                            print( repr( content ) )
                        got_one = True
                    except:
                        if not got_one: eprint( "Unexpected error:", sys.exc_info( )[0] )
                if got_one: break
            if not got_one:
                print( "Tried 15 times and could not instruct device to set up network" )
                sys.exit( )

            ### Connect (back) to main network
            if not reconnect( credentials ):
                print( "Could not reconnect to " + ssid )
                break
            rec[ 'CompletedTime' ] = time.time()

            initial_status = get_status( found, args.pause_time, args.verbose )
            if initial_status:
                print( "Confirmed device " + found + " on " + ssid + ' network' )
                for pair in settings:
                    if pair[0] in ( 'DeviceName', 'LatLng', 'TZ' ):
                        rec[ pair[0] ] = pair[1]
                finish_up_device( found, rec, 'provision', args, new_version, initial_status )
            else:
                print( "Could not find device on " + ssid + ' network' )
                break
        else:
            if args.wait_time == 0:
                print("Exiting. No additional devices found and wait-time is 0. Set non-zero wait-time to poll for multiple devices.")
                break
            if args.verbose > 0:
                print( 'Found no new devices. Waiting ' + str(args.wait_time) + ' seconds before looking again. Press ^C to cancel' )
            time.sleep( args.wait_time )

def identify( device_address ):
    toggle_device( device_address, None )

def replace_device( db_path, from_device, to_device ):
    global device_db

    for d in [ ('from', from_device ), ('to', to_device ) ]:
        if d[1] not in device_db:
            print( "--" + d[0] + " device " + d[1] + " is not stored in the device db " + db_path )
            sys.exit()

    saved = copy.deepcopy( device_db[ to_device ][ 'settings' ] )

    device_db[ to_device ][ 'settings' ] = copy.deepcopy( device_db[ from_device ][ 'settings' ] )
    for n in exclude_from_copy:
        src = saved
        dest = device_db[ to_device ][ 'settings' ]
        for k in n.split('.'):
            if k in src:
                src = src[ k ]
                if type( src ) == type( {} ):
                     if not k in dest:
                         dest[ k ] = {}
                     dest = dest[ k ]
                else:
                     dest[ k ] = src

    device_db[ to_device ][ 'actions' ] = device_db[ from_device ][ 'actions' ]
    write_json_file( db_path, device_db )
    

def factory_reset( device_address, verbose ):
    try:
        contents = json.loads( url_read( "http://" + device_address + "/settings/?reset=1" ) )
        if verbose > 1:
            print( repr( contents ) )
        print( "Reset sent to " + device_address )
    except BaseException as e:
        print( "Reset failed" )
        if isinstance( e.reason, socket.timeout ) or str( e.reason ) == '[Errno 64] Host is down':
            print( "Device is not reachable on your network" )
            return
        print( "Unexpected error:", sys.exc_info( )[0] )

####################################################################################
#   Option validation
####################################################################################

def validate_options( vars ):
    op = vars[ 'operation' ]
    incompatible = []

    allow = { "help" : [ ],
              "query" : [ "query_conditions", "query_columns", "group", "set_tag", "match_tag", "delete_tag", "refresh" ],
              "schema" : [ "query_conditions", "query_columns", "group", "match_tag", "refresh" ],
              "apply" : [ "query_conditions", "query_columns", "group", "set_tag", "match_tag", "delete_tag", 
                          "ota", "apply_urls", "refresh", "delete_device", "restore_device", "dry_run", "settings", "access" ],
              "probe-list" : [ "query_conditions", "group", "refresh", "access" ],
              "provision-list" : [ "group", "ddwrt_name", "group", "cue", "timing", "ota", "print_using", "toggle", "wait_time" ],
              "provision" : [ "ssid", "wait_time", "ota", "print_using", "toggle", "cue", "settings" ],
              "list" : [ "group" ],
              "clear-list" : [ ]
            }

    require = { "factory-reset" : [ "device_address" ],
                "identify" : [ "device_address" ],
                "flash" : [ "device_address", "ota" ],
                "ddwrt-learn" : [ "ddwrt_name", "ddwrt_address", "ddwrt_password" ],
                "import" : [ "file" ],
                "replace" : [ "from_device", "to_device" ],
                "print-sample" : [ "print_using" ]
              }

    for r in require:
         if r in allow:
             allow[ r ].extend( require[ r ] )
         else:
             allow[ r ] = require[ r ]

    for z in [ v for v in vars if vars[ v ] and v not in ( 'what', 'access', 'operation', 'ddwrt_file', 'pause_time', 'ota_timeout', 'device_db', 'prefix', 'device_queue', 'verbose' ) ]:
        if z not in allow[ op ]:
            incompatible.append( z.replace( "_", "-" ) )
    if len( incompatible ) > 1:
        print( "The options " + ( ','.join( [ "--" + w for w in list( incompatible ) ] ) ) + " are incompatible with the " + op + " operation" )
        sys.exit()
    elif len( incompatible ) == 1:
        print( "The option --" + incompatible[ 0 ] + " is incompatible with the " + op + " operation" )
        sys.exit()

    required = []
    if op in require:
        for r in require[ op ]:
            if r not in vars or not vars[ r ]:
                required.append( r.replace( "_", "-" ) )

    if len( required ) > 1:
        print( "The options " + ( ','.join( [ "--" + w for w in list( required ) ] ) ) + " are required with the " + op + " operation" )
        sys.exit()
    elif len( required ) == 1:
        print( "The option --" + required[ 0 ] + " is required with the " + op + " operation" )
        sys.exit()

####################################################################################
#   Main
####################################################################################


def main():
    global init, connect, reconnect, get_cred, router_db, device_queue, device_db
    p = argparse.ArgumentParser( description='Shelly configuration utility' )
    p.add_argument( '-w', '--time-to-wait', dest='wait_time', metavar='0', type=int, default=0, help='Time to wait on each pass looking for new devices, 0 for just once' )
    p.add_argument( '-s', '--ssid', dest='ssid', metavar='SSID', help='SSID of the current WiFi network, where devices are to be connected' )
    p.add_argument( '-p', '--time-to-pause', dest='pause_time', type=int, metavar='2', default=3, help='Time to pause after various provisioning steps' )
    p.add_argument(       '--prefix', dest='prefix', metavar='shelly', default='shelly', help='Prefix for SSID search' )
    p.add_argument( '-v', '--verbose', action='count', default=0, help='Give verbose logging output' )
    p.add_argument( '-V', '--version', action='version', version='version ' + version)
    p.add_argument( '-f', '--file', metavar='FILE', help='File to read/write using IMPORT or EXPORT operation' )
    p.add_argument( '-a', '--device-address',  metavar='TARGET-ADDRESS', help='Address or DNS name of target device' )
    p.add_argument(       '--ddwrt-name', '-N', action='append', metavar='NAME', help='Name of dd-wrt device' )
    p.add_argument( '-g', '--group',  metavar='GROUP', help='Group of devices to apply actions to (as defined in imported file)' )
    p.add_argument( '-e', '--ddwrt-address', metavar='IP-ADDRESS', help='IP address of dd-wrt device to use to configure target device' )
    p.add_argument( '-P', '--ddwrt-password', metavar='PASSWORD', help='Password for dd-wrt device' )
    p.add_argument( '-F', '--force-platform',  metavar='platform', help='Force platform choice: PC|MAC|linux', choices=('PC','MAC','linux') )
    p.add_argument( '-r', '--refresh', action='store_true', help='Refresh the db with attributes probed from device before completing operation' )
    p.add_argument(       '--access', default=None, help='Restrict apply and probe operations to Continuous, Periodic, or ALL devices', choices=['ALL','Continuous','Periodic'] )
    p.add_argument(       '--toggle', action='store_true', help='Toggle relay on devices after each is provisioned' )
    p.add_argument(       '--device-queue', default='provisionlist.json', help='Location of json database of devices to be provisioned with provision-list' )
    p.add_argument(       '--ddwrt-file', default='ddwrt_db.json', help='File to keep ddwrt definitions' )
    p.add_argument(       '--print-using', metavar='PYTHON-FILE', help='Python program file containing a function, "make_label", for labeling provisioned devices' )
    p.add_argument(       '--device-db', default='iot-devices.json', help='Device database file (default: iot-devices.json)' )
    p.add_argument(       '--ota', dest='ota', metavar='http://...|LATEST', default='', help='OTA firmware to update after provisioning, or with "flash" or "apply" operation' )
    p.add_argument( '-n', '--ota-timeout', metavar='SECONDS', default=300, type=int, help='Time in seconds to wait on OTA udpate. Default 300 (5 minutes). Use 0 to skip check (inadvisable)' )
    p.add_argument(       '--url', dest='apply_urls', action='append', help='URL fragments to apply, i.e "/settings/?lat=31.366398&lng=-96.721352"' )
    p.add_argument(       '--cue', action='store_true', help='Ask before continuing to provision next device' )
    p.add_argument(       '--timing', action='store_true', help='Show timing of steps during provisioning' )
    p.add_argument( '-q', '--query-columns', help='Comma separated list of columns to output, start with "+" to also include all default columns, "-" to exclude specific defaults' )
    p.add_argument( '-Q', '--query-conditions', help='Comma separated list of name=value selectors' )
    p.add_argument( '-t', '--match-tag', help='Tag to limit query and apply operations' )
    p.add_argument( '-T', '--set-tag', help='Tag results of query operation' )
    p.add_argument(       '--delete-tag', help='Remove tag from results of query operation' )
    p.add_argument(       '--delete-device', metavar='DEVICE-ID|ALL', help='Remove device from device-db' )
    p.add_argument(       '--restore-device', metavar='DEVICE-ID|ALL', help='Restore settings of devices matching query' )
    p.add_argument(       '--from-device', metavar='DEVICE-ID', help='Device db entry from which to copy settings using the replace operation' )
    p.add_argument(       '--to-device', metavar='DEVICE-ID', help='Device db entry to receive the copy of settings using the replace operation' )
    p.add_argument(       '--dry-run', action='store_true', help='Display urls to apply instead of performing --restore or --settings' )
    p.add_argument(       '--settings', help='Comma separated list of name=value settings for use with provision operation' )
    p.add_argument( metavar='OPERATION',
                    help='|'.join(all_operations),
                    dest="operation", 
                    choices=all_operations )

    p.add_argument( dest='what', default=None, nargs='*' )

    try:
        args = p.parse_args( )
    except BaseException as e:
        if e.code != 0:
            print( )
            print( 'Try "python automagic.py features" or "python automagic.py help" for more detailed information.' )
            print( 'Or,... "python automagic.py --help" will give a brief description of all options.' )
        sys.exit()

    validate_options( vars( args ) )

    new_version = None

    if not args.access:
        if args.operation in ( 'query' ):
            args.access = 'ALL'
        else:
            args.access = 'Continuous'

    if args.operation == 'help':
        help_docs( args.what )
        return

    if args.operation == 'features':
        print_features( )
        return

    if args.operation in [ 'ddwrt-learn' ] and len( args.ddwrt_name ) > 1:
        p.error( "only one --ddwrt-name (-N) can be specified for ddwrt-learn operation" )
        return

    if args.operation in [ 'provision-list' ] and ( not args.ddwrt_name or len( args.ddwrt_name ) > 2 ):
        p.error( "the auto-provision operation requires either one or two --ddwrt-name (-N) options" )
        return

    if args.force_platform:
        platform = args.force_platform
    else:
        if sys.platform == 'darwin':
            platform = 'MAC'
        elif sys.platform == 'win32':
            platform = 'PC'
        elif sys.platform == 'linux':
            platform = 'linux'
        else:
            platform = 'UNKNOWN'

    if platform == 'MAC':
        connect = mac_connect
        reconnect = mac_reconnect
        init = mac_init
        get_cred = mac_get_cred
    elif platform == 'PC':
        connect = pc_connect
        reconnect = pc_reconnect
        init = noop
        get_cred = pc_get_cred
    elif sys.platform == 'linux':
        if args.operation == 'provision':
            print( "provision operation is not yet supported with linux. Use provision-list instead." )
            return
    else:
        print( "Unsupported OS: " + sys.platform )
        return

    if args.ddwrt_name:
        router_db = read_json_file( args.ddwrt_file, {}, True )
        router_db[ 'format' ] = 'automagic'

    if args.operation in ( 'import', 'provision-list', 'list', 'probe-list' ):
        device_queue = read_json_file( args.device_queue, [], ['SSID','ProbeIP'] )

    if args.ota and args.ota != 'LATEST':
        if args.verbose > 0: print( "Checking version of OTA firmware" )
        try:
            contents = url_read( args.ota, 'b', tmout=60 )
        except:
             eprint( "Unexpected error:", sys.exc_info( )[0] )
             contents = None
        if not contents or not zipfile.is_zipfile( stringtofile( contents ) ):
            print( "Could not fetch OTA firmware" )
            return
        zip = zipfile.ZipFile( stringtofile( contents ) )
        manifest = None
        for z in zip.namelist():
            if z.endswith('manifest.json'):
                manifest = z
                break
        if manifest:
            f = zip.open( manifest )
            contents = json.loads( f.read( ).decode('utf8') )
            new_version = contents[ 'build_id' ]
            print( "OTA firmware build ID: " + new_version )

    if args.print_using:
        import_label_lib( args.print_using )

    if args.operation in [ 'provision-list', 'probe-list', 'query', 'apply', 'schema', 'provision', 'replace' ]:
        device_db = read_json_file( args.device_db, {}, True )
        device_db[ 'format' ] = 'automagic'

    if args.operation == 'import':
        if not args.file:
            p.error( "import operation requiress -f|--file option" )
            return
        if args.file.lower().endswith('.json'):
            import_json( args.file, args.device_queue )
        else:
            import_csv( args.file, args.device_queue )

    elif args.operation == 'provision':
        init( )
        credentials = get_cred( )
        try:
            provision( credentials, args, new_version )
        except SystemExit:
            return
        except:
            print( "Attempting to reconnect to " + credentials['ssid'] + " after failure" )
            reconnect( credentials )
            raise

    elif args.operation == 'factory-reset':
        factory_reset( args.device_address, args.verbose )

    elif args.operation == 'flash':
        flash_device( args.device_address, args.pause_time, args.verbose, args.ota, args.ota_timeout, new_version, args.dry_run )

    elif args.operation == 'ddwrt-learn':
        ddwrt_learn( args.ddwrt_name[0], args.ddwrt_address, args.ddwrt_password, args.ddwrt_file )

    elif args.operation == 'provision-list':
        provision_list( args, new_version )

    elif args.operation == 'list':
        print_list( args.device_queue, args.group )

    elif args.operation == 'clear-list':
        if args.group:
            print( "--group is not yet compatible with clear-list" )
            sys.exit()
        clear_list( args.device_queue )

    elif args.operation == 'print-sample':
         test_print( )

    elif args.operation in ( 'probe-list' ):
        probe_list( args )

    elif args.operation == 'query':
        query( args )

    elif args.operation == 'apply':
        query( args, new_version )

    elif args.operation == 'identify':
        identify( args.device_address )

    elif args.operation == 'schema':
        schema( args )

    elif args.operation == 'replace':
        replace_device( args.device_db, args.from_device, args.to_device )


if __name__ == '__main__':
    try:
        compatibility()
        main() 
    except EOFError as error:
        pass
    except KeyboardInterrupt as error:
        pass


### examples of GUI interaction with DD-WRT device
###   curl --referer http://192.168.1.1/Management.asp -d submit_button=Management -d action=Reboot -u admin:password --http1.1 -v http://192.168.1.1/apply.cgi
###   curl http://192.168.1.1/apply.cgi -d "submit_button=Ping&action=ApplyTake&submit_type=start&change_action=gozila_cgi&next_page=Diagnostics.asp&ping_ip=route+add+-net+21.5.128.0+netmask+255.255.128.0+dev+ppp0" -u admin:admin
###   curl -u admin:pw --referer http://192.168.1.1/Management.asp --http1.1 http://192.168.1.1/apply.cgi -d "submit_button=Status_Internet&action=Apply&change_action=gozila_cgi&submit_type=Disconnect_pppoe
###   curl -u admin:pw --referer http://192.168.1.1/Management.asp --http1.1 http://192.168.1.1/apply.cgi -d "submit_button=index&action=ApplyTake&change_action=&submit_type="

#def ddwrt_apply( tn, mode ):
#    """failed attempt to do everything the "apply" button in the GUI does, to avoid needing to use http/CGI approach (which takes 20s)"""
#    if mode == 'sta':
#        ddwrt_get_single_line_result( tn, "/sbin/ifconfig eth2 192.168.33.10" )
#    ddwrt_get_single_line_result( tn, "stopservice nas;stopservice wlconf;startservice wlconf 2>/dev/null;startservice nas" )
#    if mode == 'sta':
#        ddwrt_get_single_line_result( tn, "route del default netmask 0.0.0.0 dev br0" )
#        ddwrt_get_single_line_result( tn, "route add -net 192.168.33.0 netmask 255.255.255.0 dev eth2" )
#        ddwrt_get_single_line_result( tn, "route add default gw 192.168.33.1 netmask 0.0.0.0 dev br0" )
#        ddwrt_get_single_line_result( tn, "route add default gw 192.168.33.1 netmask 0.0.0.0 dev eth2" )
#    else:
#        ddwrt_get_single_line_result( tn, "route del -net 192.168.33.0 netmask 255.255.255.0 dev eth2" )
#        ddwrt_get_single_line_result( tn, "route del default gw 192.168.33.1 netmask 0.0.0.0 dev br0" )
#        ddwrt_get_single_line_result( tn, "route del default gw 192.168.33.1 netmask 0.0.0.0 dev eth2" )
