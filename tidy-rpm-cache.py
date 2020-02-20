#!/usr/bin/python3 -s
# -*- coding: utf-8 -*-

""" Deletes obsolete RPM package files from a directory.
Based on tidy-rpm-cache.py rev 1225.

Copyright:

Copyright (C) 2008-2009 Darwin Slattery
Copyright (C) 2019      Jani Välimaa

License:

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.


Usage:

tidy-rpm-cache.py {-d|--dir=dir}
                  {-n|--num-obsolete=number}
                  {-x|--exclude=reg-ex}
                  {-f|--force}
                  {--ignore-arch}
                  {--ignore-file-errors}
                  {--log-prefix=text}
                  {-s|--srpm}
                  {-u|--usage} {-h|--help} {--version}
                  {-v|--verbose} {-q|--quiet}

This script deletes obsolete files by comparing the version information
of all RPM package files which provide the same software package. You can
specify any number of paths of directories to search and you can also
exclude specific packages from being tested for obsolescence.

To run this script simply specify the path of a directory containing
RPM package files using the '--dir' option. For example, to delete obsolete
RPMs from the directory '/tmp/packages', execute the following command:

tidy-rpm-cache.py --dir=/tmp/packages

The script will display a list of RPM packages it has deemed as obsolete
and ask for confirmation before deleting them from the filesystem. To
disable the confirmation message, add the '--force' option.

You can also configure the script to keep a specific number of obsolete
versions of a package. For example, if you wish to keep one obsolete
version of each package in case the newest version causes problems, you
can achieve this using the following command:

tidy-rpm-cache.py --dir=/tmp/packages --num-obsolete=1

Note that the --num-obsolete option specifies the number of versions
to keep excluding the newest version of the package. In this case all but
the newest and the second newest versions would be deleted.

To prevent the deletion of specific packages you can supply a regular
expression which will be tested against each RPM package filename. If the
expression matches, then that RPM will be excluded from the obsolescence
test. For example, to exclude all kernel packages, execute the following
command:

tidy-rpm-cache.py --dir=/tmp/packages --exclude='^kernel.*'

Note: always enclose the regular expressions in single quotes to prevent
them being interpreted as a glob expression.

To see more information about what the script is doing and what packages it
is examining, add the '--verbose' option. To disable all output except
warning and error messages, add the '--quiet' option.

For more information on these and other options, please see the section
called 'Options' below.


Minimising the Size of a YUM Cache Directory:

The reason for writing this script was to provide a feature missing in the
current implementation of YUM. YUM is an RPM-based software management
system which provides an option to keep downloaded package files in a cache
directory for later use. It does not however provide a feature to delete
package files which have become obsolete because a newer version of the same
package has been downloaded. The following command could be executed
manually or from a cron script to clean the default cache directory on
Fedora Linux systems:

tidy-rpm-cache.py --dir=/var/cache/yum --force


Options:

-d, --dir         =<dir> The path of a directory to search recursively for
                         RPM files. This option can be specified multiple
                         times. If this option is not specified, the
                         current directory is searched.

-x, --exclude  =<reg-ex> Exclude package filenames which match this
                         regular expression from being checked. This option
                         can be specified multiple times.

-f, --force              Do not confirm before deleting obsolete RPM package
                         files.

-h, --help               Display help information.

    --ignore-arch        Compare all files with the same package name
                         regardless of whether their architectures differ

    --ignore-file-errors Do not print errors relating to reading RPM package
                         files

    --log-prefix =<text> Prepend text to the start of every information,
                         warning, and error message.

-n, --num-obsolete=<int> The maximum number of obsolete versions of a
                         package to keep. Note that the default value is 0
                         meaning that all but the newest version of a
                         package will be deleted.

-q, --quiet              Do not display any information during execution
                         except warnings and error messages.

-s, --srpm               Check for obsolete source RPMs instead of normal
                         RPMs.

-u, --usage              Display usage information

-v, --verbose            Increase the amount of information displayed
                         during execution.

    --version            Display version information
"""

"""
Code Information:

The following outlines the basic control flow in this script.

-> main()
    |-> tidy-rpm-cache()
        | create RunData object to contain obsolete paths and other stats
        | parse command line arguments
        |-> find_rpms() in all search directories
        | Create an RPM transaction set
        |-> find_obsolete_rpms()
            | read RPM header data from file
            |-> cmp_RpmData_by_version
                |-> rpm.versionCompare()
            | if more than num_obsolete versions exist for a package:
                |-> display_pkg_summary()
                | add obsolete RPM paths to RunData
        |
        | if obsolete paths in RunData:
            |-> delete_obsolete_rpms()
                | Confirm delete operation with user.
                | Delete each file from the file system
        | exit
"""

__author__          = "Jani Välimaa (wally [AT] mageia.org)"
__date__            = "02/09/2019"
__copyright__       = "2008-2009 Darwin Slattery, 2019 Jani Välimaa"
__license__         = "GPLv3"
__version__         = "Version: 1500".split( ' ' )[ 1 ]


import sys
import os
from os.path import join, basename
import logging
import getopt
import traceback
from time import gmtime, strftime
import rpm
import re
from functools import cmp_to_key


# The global information, warning, and error message target.
g_logger            = None
# Flag indicating if package architectures should be ignored.
g_ignore_arch       = False
# Flag indicating if the header of the results has already been displayed.
g_display_header    = True


class RpmData:
    """ Encapsulates RPM header and path information for a RPM file.

    Members:
    header -- The RPM header.
    path -- The path of the RPM file (string).
    size -- The size of the RPM file.
    """

    def __init__( self ):
        """ Constructor for RpmData instances. """
        self.header = None
        self.path = ""
        self.size = -1

    def __init__( self
                  , header
                  , path ):
        """ Constructor for RpmData instances. """
        self.header = header
        self.path = path
        self.size = -1


class RunData:
    """ Encapsulates information relating to the number and size of packages
    processed during this run of the script.

    """

    def __init__( self ):
        """ Default constructor for RunData instances.

        Members:
        obs_paths -- The paths of RPM files deemed to obsolete.
        file_errors -- The errors related to file reading.
        total_found -- The total number of RPM files found.
        total_obs_size -- The total size (in bytes) of RPM files deleted.

        """
        self.obs_paths = []
        self.file_errors = []
        self.total_found = 0
        self.total_obs_size = 0


def cmp_RpmData_by_version( a, b ):
    """ Wrapper function which passes the RPM headers in two RpmData objects
        to the rpm.versionCompare function.

    Returns:
    1 -- if the first RPM file is a newer version than the second.
    0 -- if both RPM files provide the same version of the package.
    -1 -- if the first RPM file is an older version than the second.
    """
    return rpm.versionCompare( a.header, b.header )


def cmp(a, b):
    return (a > b) - (a < b)

def cmp_paths_by_filename( a, b ):
    """ Compares paths based on the filename part only.

    Returns:
    1 -- if the filename in the first path is greater than the second.
    0 -- if the filename in the first path is equal to the second.
    -1 -- if the filename in the first path is less than the second.
    """
    return cmp( basename( a ), basename( b ) )


def cmp_paths_by_pkg_name_and_arch( a, b ):
    """ Compares paths based on the name and architecture of the package.

    Returns:
    1 -- if the filename in the first path is greater than the second.
    0 -- if the filename in the first path is equal to the second.
    -1 -- if the filename in the first path is less than the second.

    The code works best with RPM packages which adhere to the following
    filename template:
        [PACKAGE_NAME]-[MAJOR].[MINOR]-[REVISION].[OS].[ARCH].rpm

    This is the template used for most Fedora packages. If the filename is
    structured differently, the cmp_paths_by_filename function is used.
    Developers may wish to redesign this function or add there own to suit other
    filename template.
    """

    result = 0
    a_parts = basename( a ).split( '.' )
    b_parts = basename( b ).split( '.' )

    if len( a_parts ) > 2 and len( b_parts ) > 2:
        # Compare the architecture part.
        result = cmp( a_parts[ len( a_parts ) - 2 ]
                    , b_parts[ len( b_parts ) - 2 ] )
        if result == 0:
            # Compare the parts containing the package and the version data.
            if len( a_parts ) > 3 and len( b_parts ) > 3:
                result = cmp( a_parts[ 0:( len( a_parts ) - 3 ) ]
                              , b_parts[ 0:( len( b_parts ) - 3 ) ] )
            else:
                cmp_paths_by_filename( a, b )
    else:
        result = cmp_paths_by_filename( a, b )

    return result


def tidy_rpm_cache( argV ):
    """ The main driver function for this script.

    Keyword arguments:
    argV -- The list of command-line arguments.

    This function sets default configuration values, parses the command-line
    arguments, and executes the process_search_dir for each search directory
    specified.

    Returns nothing.
    """
    global g_logger
    global g_ignore_arch


    # Create container object for obsolete paths and other statistics.
    run_data            = RunData()
    # The directory in which to search for RPMs.
    search_dir_paths    = []
    # Number of obsolete versions of a package to allow.
    num_obsolete        = 0
    # The packages which are excluded.
    excluded            = []
    # Flag indicating that script should search for obsolete SRPMS.
    srpm_mode           = False
    # Flag indicating that user should not have to confirm deletion.
    force_del           = False
    # Flag indicating RPM headers should be validated.
    verify_headers      = False
    # Flag indicating that errors relating reading files should be ignored.
    ignore_file_errors  = False
    # The verbosity of information messages.
    logging_level       = logging.INFO
    # The text to print at the start of each information, warning, and error
    # message.
    log_prefix          = ""

    # Set up basic logging.
    g_logger = logging.getLogger()
    log_stream = logging.StreamHandler()
    log_stream.setFormatter(
        logging.Formatter( '[%(levelname)s] %(message)s' ) )
    g_logger.addHandler( log_stream )
    g_logger.setLevel( logging_level )

    # Parse command-line arguments.
    try:
        opts, args = getopt.getopt( argV
                                    , 'd:fhin:qsuvx:'
                                    , [ 'dir='
                                        , 'exclude='
                                        , 'force'
                                        , 'help'
                                        , 'ignore-file-errors'
                                        , 'ignore-arch'
                                        , 'log-prefix='
                                        , 'num-obsolete='
                                        , 'quiet'
                                        , 'srpm'
                                        , 'usage'
                                        , 'verbose'
                                        , 'verify-headers'
                                        , 'version' ] )
    except getopt.GetoptError as e:
        g_logger.error( str( e ) )
        display_usage()
        sys.exit( 2 )

    # Store command-line argument values.
    for opt, arg in opts:
        if opt in ( '-d', '--dir' ):
            search_dir_paths.append( arg )

        if opt in ( '-x', '--exclude' ):
            excluded.append( arg )

        if opt in ( '-f', '--force' ):
            force_del = True

        if opt in ( '', '--log-prefix' ):
            log_prefix = arg

        if opt in ( '-h', '--help' ):
            display_help()
            sys.exit()

        if opt in ( '-n', '--num-obsolete' ):
            try:
                num_obsolete = int( arg )
            except ( ValueError ):
                g_logger.error( "Invalid num-obsoletes value '" + arg + "'" )
                display_usage()
                sys.exit( 1 )

        if opt in ( '-i', '--ignore-file-errors' ):
            ignore_file_errors = True

        if opt in ( '', '--ignore-arch' ):
            g_ignore_arch = True

        if opt in ( '-q', '--quiet' ):
            logging_level = logging.WARNING

        if opt in ( '-s', '--srpm' ):
            srpm_mode = True

        if opt in ( '-u', '--usage' ):
            display_usage()
            sys.exit()

        if opt in ( '-v', '--verbose' ):
            logging_level -= 10

        if opt in ( '', '--verify-headers' ):
            verify_headers = True

        if opt in ( '', '--version' ):
            display_version()
            sys.exit()

    # Adjust logging configuration using new option values.
    if logging_level > logging.DEBUG:
        g_logger.setLevel( logging_level )
    else:
        g_logger.setLevel( logging.DEBUG )
    if len( log_prefix ) > 0:
        log_stream.setFormatter(
            logging.Formatter( log_prefix + "[%(levelname)s] %(message)s" ) )

    if g_logger.getEffectiveLevel() <= logging.INFO:
        display_version()
        display_disclaimer()

    # If no search directories were specified, use the current directory.
    if len( search_dir_paths ) == 0:
        search_dir_paths.append( '.' )

    if num_obsolete < 0:
        g_logger.warn( "Number of obsoletes cannot be negative, setting to 0" )
        num_obsolete = 0

    # Check and compile all regular expressions for excluded package names.
    reg_ex_objects = []
    for reg_ex in excluded:
        try:
            pattern = re.compile( reg_ex )
            reg_ex_objects.append( pattern )
        except re.error as e:
            g_logger.warning( "The expression '%s' could not be compiled: %s"
                % ( reg_ex, str( e ) ) )

    # Generate a list of all RPM paths in the search directories.
    rpm_paths = find_rpms( search_dir_paths
                           , reg_ex_objects
                           , srpm_mode )
    run_data.total_found = len( rpm_paths )
    if run_data.total_found > 0:
        g_logger.debug( "Found %d RPM files." % ( run_data.total_found ) )
    else:
        g_logger.info( "No RPM files were found." )
        return

    # Create an RPM transaction set.
    rpm_trans_set = rpm.TransactionSet()
    if not verify_headers:
        rpm_trans_set.setVSFlags( rpm.RPMVSF_NODSA | rpm.RPMVSF_NODSAHEADER )

    # Sort the list of RPM paths by filename.
    if g_ignore_arch:
        rpm_paths.sort( key = cmp_to_key(cmp_paths_by_filename) )
    else:
        rpm_paths.sort( key = cmp_to_key(cmp_paths_by_pkg_name_and_arch) )

    # Identify the obsolete files and add them to run_data.obs_paths.
    find_obsolete_rpms( rpm_paths
                        , run_data
                        , rpm_trans_set
                        , num_obsolete )

    if not ignore_file_errors and len( run_data.file_errors ) > 0:
        g_logger.warn( "%d file errors occurred. These are listed below." %
                        len( run_data.file_errors ) )
        for file_error in run_data.file_errors:
            g_logger.warn( file_error )

    # Ask for user confirmation before deleting.
    if len( run_data.obs_paths ) > 0:
        delete_obsolete_rpms( run_data, force_del )
    else:
        g_logger.info( "No old RPMs were found." )


def find_rpms( search_dir_paths
               , excluded
               , srpm_mode ):

    """ Generates a list of the RPM package files found in directories.

    Keyword arguments:
    search_dir_paths -- The list of directories to search.
    excluded -- A list of regular expressions to exclude from the results.
    srpm_mode -- Search for .src.rpm files instead of .rpm files.

    Returns a list of paths to RPM files.
    """
    global g_logger
    results = list()

    for dir_path in search_dir_paths:
        g_logger.debug( "Searching directory '" + dir_path + "'" )
        for root, dirs, files in os.walk( dir_path ):
            for file_name in files:
                if not os.path.isfile( os.path.join(root, file_name ) ):
                    continue

                if os.path.islink( os.path.join(root, file_name ) ):
                    continue

                if file_name.endswith( ".rpm" ):
                    if file_name.endswith( ".src.rpm" ):
                        if not srpm_mode:
                            continue
                    elif srpm_mode:
                        continue
                else:
                    continue

                is_excluded = False
                for reg_ex in excluded:
                    if reg_ex.search( file_name ):
                        is_excluded = True
                        break
                if is_excluded:
                    g_logger.debug( "Excluding " + file_name )
                    continue

                g_logger.debug( "Found '" + file_name + "'" )
                results.append( os.path.join(root, file_name ) )

    return results


def find_obsolete_rpms( rpm_paths
                        , run_data
                        , rpm_trans_set
                        , num_obsolete ):
    """ Identifies the obsolete files in a list of RPM package files.

    Keyword arguments:
    rpm_paths -- A sorted list of RPM pacakge file paths.
    run_data -- A RunData object in which to store the obsolete paths.
    rpm_trans_set -- A valid RPM transaction set.
    num_obsolete -- The maximum number of obsolete versions allowed for each
    package.

    Returns nothing.

    """
    global g_logger
    global g_ignore_arch

    last_package_tag = ''
    rpm_data_list = []

    for path in rpm_paths:
        # Read the header from the RPM file.
        rpm_hdr = None
        try:
            rpm_fd = os.open( path, os.O_RDONLY )
            rpm_hdr = rpm_trans_set.hdrFromFdno( rpm_fd )
            os.close( rpm_fd )
        except os.error as e:
            run_data.file_errors.append(
                "Unable to open file: '" + path + "'\nReason: " + str( e ) )
        except rpm.error as e:
            run_data.file_errors.append(
                "Unable to read RPM file: '" + path + "'\nReason: " + str( e ) )

        if rpm_hdr == None:
            continue

        # If the current RPM package name differs to the previous one, then we
        # can assume we have processed all RPM files which provide the previous
        # package.
        # g_logger.debug( "Package '%s'" % ( rpm_hdr[ 'name' ] ) );
        current_rpm_tag = rpm_hdr[ 'name' ]
        if not g_ignore_arch:
            current_rpm_tag += rpm_hdr[ 'arch' ]

        if current_rpm_tag != last_package_tag and last_package_tag != '':
            if len( rpm_data_list ) > 0:
                process_rpm_group( rpm_data_list, run_data, num_obsolete );
            elif last_package_tag != '':
                g_logger.debug( "Package '%s': %d total, 0 obsolete" % \
                    ( last_package_tag, list_length ) )

            # Delete all the data about the old package since we will not need
            # it again.
            del rpm_data_list[:]

        # Add the current package data to the list and remember its package
        # name.
        rpm_data_list.append( RpmData( rpm_hdr, path ) )
        last_package_tag = current_rpm_tag

    # End of 'for path in rpm_paths'.

    # Process any remaining rpms in rpm_data_list.
    if len( rpm_data_list ) > 0:
        process_rpm_group( rpm_data_list, run_data, num_obsolete );
    elif last_package_tag != '':
        g_logger.debug( "Package '%s': %d total, 0 obsolete" % \
                      ( last_package_tag, list_length ) )


def process_rpm_group( rpm_data_list, run_data, num_obsolete ):
    global g_logger
    global g_display_header

    list_length = len( rpm_data_list )
    if list_length <= ( num_obsolete + 1 ):
        return;

    package_name = rpm_data_list[ 0 ].header[ 'name' ]
    g_logger.debug( "Package '%s': %d total, %d obsolete)" % \
                    ( package_name
                    , list_length
                    , list_length - ( num_obsolete + 1 ) ) )

    # Sort the list of packages by version descending.
    rpm_data_list.sort( key = cmp_to_key(cmp_RpmData_by_version) )
    rpm_data_list.reverse()

    # Display the current and obsolete versions of this package.
    if g_logger.getEffectiveLevel() <= logging.INFO:
        if g_display_header:
            display_pkg_info_headings()
            g_display_header = False
        display_pkg_summary( rpm_data_list, num_obsolete )

    # Mark all but the num_obsolete most-recent versions for
    # deletion.
    for obs_data in rpm_data_list[ ( num_obsolete + 1 ):list_length ]:
        run_data.obs_paths.append( obs_data.path )
        if obs_data.size < 0:
            obs_data.size = os.path.getsize( obs_data.path )
        run_data.total_obs_size += obs_data.size


def delete_obsolete_rpms( run_data, force_del ):
    """ Confirms with user and deletes RPM files from the filesystem.

    Keyword arguments:
    run_data -- A RunData object containing a list of obsolete paths.
    force_del -- Do not confirm with user before deleting.

    Returns nothing.
    """
    global g_logger

    if len( run_data.obs_paths ) == 0:
        return

    g_logger.info( "" )
    g_logger.info(
        "Marked %d RPM files with a total size of %.2fM for deletion." \
        % ( len( run_data.obs_paths ), run_data.total_obs_size / 1048576.0 ) )
    user_choice=''
    if not force_del:
        while user_choice.lower() != 'y' and \
                user_choice.lower() != 'n':
            try:
                user_choice = eval(input( "\n[INFO] Are you sure you want to" + \
                                            " permanently delete these" + \
                                            " files y/n? " ))
            except KeyboardInterrupt as e:
                return

    # Delete the files from the file system.
    if force_del or user_choice.lower() == 'y':
        g_logger.info( "Deleting RPM files..." )
        for file_path in run_data.obs_paths:
            g_logger.debug( "Deleting path '" + file_path + "'" )
            try:
                os.remove( file_path )
            except os.error as e:
                g_logger.error( "Unable to delete RPM file. " + str( e ) )
                sys.exit( 1 )


def display_pkg_summary( rpm_data_list, num_obsolete ):
    """ Logs a summary of the RPMs for a package, including which will be
        deleted.

    Keyword arguments:
    rpm_data_list: A list of RpmData objects sorted newest to oldest.
    num_obsolete: The number of allowed obsolete versions.

    Returns nothing.
    """
    global g_logger
    global g_ignore_arch

    if g_ignore_arch:
        g_logger.info( rpm_data_list[ 0 ].header[ 'name' ] )
    else:
        g_logger.info( "%s (%s)" % ( rpm_data_list[ 0 ].header[ 'name' ]
                                     , rpm_data_list[ 0 ].header[ 'arch' ] ) )

    for rpm_data in rpm_data_list[ 0:( num_obsolete + 1 ) ]:
        display_pkg_info( rpm_data, "Keep" )
    for rpm_data in rpm_data_list[ ( num_obsolete + 1 ):len( rpm_data_list ) ]:
        display_pkg_info( rpm_data, "Delete" )


def display_pkg_info_headings():
    """ Prints the heading row in the package information summary table. """
    global g_logger

    max_width = 70
    g_logger.info( "=" * max_width )
    g_logger.info( "Package" )
    g_logger.info(
        "    Version                            Build Date     Size   Action" )
    g_logger.info( "=" * max_width )


def display_pkg_info( rpm_data, action ):
    """ Logs a description of an RPM in a tabular format.

    Keyword arguments:
    rpm_data -- A RpmData containing a valid RPM header and file path.
    action -- The action that will be taken e.g. "Keep" or "Delete"

    Returns nothing.

    """
    global g_logger
    global g_ignore_arch

    max_width = 70
    widths = [ 34, 11, 7, 8 ]
    assert( sum( widths ) < max_width )
    format_string = "    %" + \
                    str( widths[ 0 ] ) + "s " + \
                    "%" + str( widths[ 1 ] ) + "s " + \
                    "%" + str( widths[ 2 ] ) + ".2fM " + \
                    " %" + str( widths[ 3 ] ) + "s";
    version_string = '%s-%s' % ( rpm_data.header[ 'version' ]
                                 , rpm_data.header[ 'release' ] )
    if g_ignore_arch:
        version_string += "." + rpm_data.header[ 'arch' ]

    build_date = strftime( '%d %b %Y'
                           , gmtime( rpm_data.header[ 'buildtime' ] ) )
    if rpm_data.size < 0:
        rpm_data.size = os.path.getsize( rpm_data.path )
    size = rpm_data.size / 1048576.0

    # Left justify text columns.
    if len( version_string ) < widths[ 0 ]:
        version_string += ' ' * ( widths[ 0 ] - len( version_string ) )
    elif len( version_string ) > widths[ 0 ]:
        # Note: we have to indent 7 on new lines for the log prefix text.
        version_string += "\n" + " " * ( widths[ 0 ] + 4 + 7 )
    if len( build_date ) < widths[ 1 ]:
        build_date += ' ' * ( widths[ 1 ] - len( build_date ) )
    if len( action ) < widths[ 3 ]:
        action += ' ' * ( widths[ 3 ] - len( action ) )

    g_logger.info( format_string % \
                    ( version_string
                      , build_date
                      , size
                      , action ) )


def display_help():
    """ Prints help information for this script. """
    print( """

    tidy-rpm-cache.py - Deletes obsolete RPM package files in a directory.

    Usage:""" )

    display_usage()

    print(( """
    This script deletes obsolete files by comparing the version information
    of all RPM package files which provide the same software package. You can
    specify any number of paths of directories to search and you can also
    exclude specific packages from being tested for obsolescence.

    To run this script simply specify the path of a directory containing
    RPM package files using the '--dir' option. For example, to delete obsolete
    RPMs from the directory '/tmp/packages', execute the following command:

    tidy-rpm-cache.py --dir=/tmp/packages

    The script will display a list of RPM packages it has deemed as osolete
    and ask for confirmation before deleting them from the filesystem. To
    disable the confirmation message, add the '--force' option.

    You can also configure the script to keep a specific number of obsolete
    versions of a package. For example, if you wish to keep one obsolete
    version of each package in case the newest version causes problems, you
    can achieve this using the following command:

    tidy-rpm-cache.py --dir=/tmp/packages --num-obsolete=1

    Note that the --num-obsolete option specifies the number of versions
    to keep excluding the newest version of the package. In this case all but
    the newest and the second newest versions would be deleted.

    To prevent the deletion of specific packages you can supply a regular
    expression which will be tested against each RPM package filename. If the
    expression matches, then that RPM will be excluded from the obsolescence
    test. For example, to exclude all kernel packages, execute the following
    command:

    tidy-rpm-cache.py --dir=/tmp/packages --exclude='^kernel.*'

    Note: always enclose the regular expressions in single quotes to prevent
    them being interpreted as a glob expression.

    To see more information about what the script is doing and what packages it
    is examining, add the '--verbose' option. To disable all output except
    warning and error messages, add the '--quiet' option.

    For more information on these and other options, please see the section
    called 'Options' below.


    Minimising the Size of a YUM Cache Directory:

    The reason for writing this script was to provide a feature missing in the
    current implementation of YUM. YUM is an RPM-based software management
    system which provides an option to keep downloaded package files in a cache
    directory for later use. It does not however provide a feature to delete
    package files which have become obsolete because a newer version of the same
    package has been downloaded. The following command could be executed
    manually or from a CRON script to clean the default cache directory on
    Fedora Linux systems:

    tidy-rpm-cache.py --dir=/var/cache/yum


    Options:
    -d, --dir         =<dir> The path of a directory to search recursively for
                             RPM files. This option can be specified multiple
                             times. If this option is not specified, the
                             current directory is searched.

    -x, --exclude  =<reg-ex> Exclude package filenames which match this
                             regular expression from being checked. This option
                             can be specified multiple times.

    -f, --force              Do not confirm before deleting obsolete RPM package
                             files.

    -h, --help               Display help information.

        --ignore-arch        Compare all files with the same package name
                             regardless of whether their architectures differ

        --ignore-file-errors Do not print errors relating to reading RPM package
                             files

        --log-prefix =<text> Prepend text to the start of every information,
                             warning, and error message.

    -n, --num-obsolete=<int> The maximum number of obsolete versions of a
                             package to keep. Note that the default value is 0
                             meaning that all but the newest version of a
                             package will be deleted.

    -q, --quiet              Do not display any information during execution
                             except warnings and error messages.

    -s, --srpm               Check for obsolete source RPMs instead of normal
                             RPMs.

    -u, --usage              Display usage information

    -v, --verbose            Increase the amount of information displayed
                             during execution.

        --version            Display version information

    Copyright:

    Copyright (C) """ + __copyright__ + """


    License:

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.


    """ ))


def display_usage():
    """ Prints usage information for this script. """
    print( """
    tidy-rpm-cache.py {-d|--dir=dir}
                      {-n|--num-obsolete=number}
                      {-x|--exclude=reg-ex}
                      {-f|--force}
                      {--ignore-arch}
                      {--ignore-file-errors}
                      {--log-prefix=text}
                      {-s|--srpm}
                      {-u|--usage} {-h|--help} {--version}
                      {-v|--verbose} {-q|--quiet}
    """ )


def display_version():
    """ Prints version information for this script. """
    global g_logger

    g_logger.info( "tidy-rpm-cache.py rev%s, Copyright (C) %s" %
                    ( __version__, __copyright__ ) )

def display_disclaimer():
    """ Prints a summary of the license. """
    global g_logger

    g_logger.info( "This program comes with ABSOLUTELY NO WARRANTY." )
    g_logger.info( "This is free software, and you are welcome to" + \
                 " redistribute it under certain conditions." )
    g_logger.info( "For details type 'tidy-rpm-cache.py --help'." )


def main( argV ):
    """ A wrapper function which calls the main driver function and catches any
    unhandled exceptions.

    Keyword arguments:
    argV -- The list of command-line arguments.

    """
    global g_logger

    try:
        tidy_rpm_cache( argV )
    except Exception as e:
        if g_logger == None:
            logging.basicConfig()
            g_logger = logging.getLogger()

        g_logger.error( "The script failed because an exception occurred." )
        g_logger.error( "For more information see the details below." )
        cla, exc, trbk = sys.exc_info()
        traceback.print_exception( cla, exc, trbk )
        sys.exit( 1 )


if __name__ == "__main__":
    main( sys.argv[ 1: ] )
