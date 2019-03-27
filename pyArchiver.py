#!/usr/bin/env python3
# coding: utf8

# Copyright (C) 2019 Christophe Meneboeuf <christophe@xtof.info>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program. If not, see <http://www.gnu.org/licenses/>.

import sys
import os
import platform
import argparse
import json
import configparser
import tempfile
import tarfile
import shutil
import binascii
import random
from io import BytesIO
from time import localtime, strftime
import re

# package: pycryptodome
from Crypto.Cipher import AES
from Crypto.Util import Counter
from Crypto.Protocol import KDF
from Crypto.Random import get_random_bytes

# package: paramiko (ssh & sftp)
import paramiko
    # only to hide a paramiko warning
import cryptography
import warnings

# SQL
import sqlite3


### JSON KEYS
JSON_KEY_GENERATOR = "Generator"
JSON_KEY_ROOT = "root"
JSON_KEY_IDENTICAL = "identical"
JSON_KEY_DIFFERENT = "different"
JSON_KEY_UNIQUE_LEFT = "unique left"
JSON_KEY_UNIQUE_RIGHT = "unique right"
JSON_KEY_RENAMED = "renamed and duplicates"
JSON_KEY_LEFT = "left"
JSON_KEY_RIGHT = "right"
JSON_KEY_FILES = "files"
JSON_KEY_HASH = "hash"
JSON_KEY_TIME = "last_modified"
JSON_KEY_SIZE = "size"


### TOOLS

NO_ERROR = 0
Errors = []

# Fatal Error
def Error_Fatal(msg):
    print("Error: " + msg)
    sys.exit(-1)


# Recoverable Error: displaying and logging
def Error(msg):
    Errors.append(msg)
    print(msg)

# Prints errors that where logged
def PrintErrors():
    if len(Errors) != 0:
        print("\n\n!!!!!!!!! {} errors happened !!!!!!!!\n\n".format(len(Errors)))
        for idx, err in enumerate(Errors):
            print("{}. {}".format(idx+1, err))


# Gets an executable name (Windows vs *nix)
def GetExeName(name):
    if "windows" in platform.system().lower():
        return name + ".exe"
    else:
        return "./" + name

# Creates a JSON string for an empty folder scan
def CreateEmptyJson(root):

    obj_json ={}
    obj_json[JSON_KEY_GENERATOR] = "info.xtof.COMPARE_FOLDERS"
    obj_json[JSON_KEY_ROOT] = root
    obj_json[JSON_KEY_FILES] = []
    obj_json[JSON_KEY_HASH] = "fast"
    return json.dumps(obj_json, sort_keys=True, indent=4)


'''
Class to store the state of the archive
'''
class Storage:

    def __init__(self, file_db):
        if not os.path.isfile(file_db):
            self.__connection =  sqlite3.connect(file_db)
            cmd = self.__connection .cursor()
            cmd.execute(''' CREATE TABLE json
                            (state_dir BLOB,
                            CONSTRAINT unique_state UNIQUE(state_dir))''')
            cmd.execute(''' CREATE TABLE config
                            (ini TEXT UNIQUE)''')
            cmd.execute(''' CREATE TABLE files_to_archive
                (path TEXT, size INTEGER)''')
            cmd.execute(''' CREATE TABLE tars
                (path TEXT)''')
            self.__connection .commit()
        else:
            self.__connection =  sqlite3.connect(file_db)            

    def __exit__(self, exc_type, exc_value, traceback):
        self.__connection.commit()
        self.__connection.close()

    # Sets the sender's type
    def setSender(self, sender):
        sender.dbInit(self.__connection)

    # Sets the cipher's type
    def setCypher(self, cipher):
        cipher.dbInit(self.__connection)

    # Returns the concrete "fetcher", that will fetch the archive files
    def getFetcher(self):
        try:
            cmd = self.__connection .cursor()
            cmd.execute('SELECT type from sender LIMIT 0,1')
            type_sender = cmd.fetchone()[0]
            if type_sender == "local":
                cmd.execute('SELECT dir_out from sender LIMIT 0,1')
                out_dir = cmd.fetchone()[0]
                return RetrieverLocal(out_dir)
            else:
                 Error_Fatal("Sender type unknown")
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])

    # Returns the concrete "cipher", that will fetch the archive files
    def getDeCypher(self):
        try:
            cmd = self.__connection .cursor()
            cmd.execute('SELECT type from cipher LIMIT 0,1')
            type_decipher = cmd.fetchone()[0]
            if type_decipher == 'aes':
                cmd.execute('SELECT key from cipher LIMIT 0,1')
                key = cmd.fetchone()[0]
                return DecipherAes(key)
            else:
                 Error_Fatal("Sender type unknown")
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])


    # Returns the names of the archive files
    def getArchives(self):
        try:
            cmd = self.__connection .cursor()
            cmd.execute('SELECT path from tars ORDER BY path')
            archives = cmd.fetchall()
            return archives
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])

    # Sets state of the archived dir. The json file is saved as a blob
    def setState(self, file_json):
        try:
            with open(file_json, 'rb') as json:
                blob = json.read()
            cmd = self.__connection .cursor()
            cmd.execute('SELECT state_dir from json LIMIT 0,1')
            json = cmd.fetchone()
            if not json is None:
                cmd.execute('DELETE from json')                
            cmd.execute('''INSERT INTO json VALUES(?)''',[memoryview(blob)])
            self.__connection.commit()
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])
        except OSError as e:
            Error_Fatal("{}\n{}\n".format(e.strerror, e.filename))


    # Retrieve the previous state of the archived dir.
    def getState(self):
        try:
            cmd = self.__connection .cursor()
            cmd.execute('SELECT state_dir from json LIMIT 0,1')
            json = cmd.fetchone()[0]
            return json
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])


    # Sets the config
    def setConfig(self, file_config):
        with open(file_config, 'r') as config:
            config = config.read()
            self.__connection.execute('INSERT INTO config VALUES(?)', [config])
            self.__connection.commit()

    # Retrieve the config
    def getConfig(self):
        try:
            cmd = self.__connection .cursor()
            cmd.execute('SELECT ini from config LIMIT 0,1')
            config = cmd.fetchone()[0]
            return config
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])

    # Sets a list a files to be archived
    def setListFiles(self, list_files):
        try:
            for file in list_files:
                self.__connection.execute('INSERT INTO files_to_archive VALUES(?,?)', [file["path"], file["size"]])
            self.__connection.commit()
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])


    # Retreve the list a files that are stiil to be archived
    def getListFiles(self):
        try:
            files_to_archive = []
            cmd = self.__connection .cursor()
            cmd.execute('SELECT * from files_to_archive')
            info_files = cmd.fetchall()
            for info in info_files:
                files_to_archive.append({
                    "path": info[0],
                    "size": info[1]
                })
            return files_to_archive
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])
    

    # Logs a successfully saved tar file
    def addTar(self, name_tar):
        try:
            self.__connection.execute('''INSERT INTO tars VALUES(?)''', [name_tar])
            self.__connection.commit()
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])

    def removeFiles(self, list_files):
        try:
            for file in list_files:
                self.__connection.execute('''DELETE FROM files_to_archive WHERE path = ?''', (file,))
            self.__connection.commit()
        except sqlite3.Error as e:
            Error_Fatal(e.args[0])
        


class DecypherDummy:
    def __call__(self, tar):
        return tar
    
    def getExtension(self):
        return ''


class DecipherAes:
    def __init__(self, password):
        self.password = password
    
    def __call__(self, archive):
        print("Deciphering")
        nonce = archive[:16]
        salt = archive[16:16+8]
        ctr_aes = Counter.new(128, initial_value=int(binascii.hexlify(nonce), 16))
        key = KDF.PBKDF2(self.password, salt)
        cipher = AES.new(key, AES.MODE_CTR, counter=ctr_aes)
        return cipher.decrypt(archive[16+8:])
    
    def getExtension(self):
        return '.aes'


'''
Abstract Cypher class
'''
class ACypher:
    def __init__(self, type):
        self.type = type
        self.KEY = b''
        self.password = b''  # unsalted key as provided

    # Inits the provided db with relevant info
    def dbInit(self, connection):
        cmd = connection .cursor()
        cmd.execute(''' CREATE TABLE IF NOT EXISTS cipher
            (type TEXT, key TEXT)''')
        cmd.execute('SELECT type from cipher LIMIT 0,1')
        type_decipher = cmd.fetchone()
        if type_decipher is None:
            cmd.execute('''INSERT INTO cipher VALUES(?,?)''', [self.type, self.password])
        connection.commit()
        return NO_ERROR 
    
    def getExtension(self):
        if self.type == "dummy":
            return ''
        else:
            return '.{}'.format(self.type)


class CypherDummy(ACypher):
    def __init__(self):
        ACypher.__init__(self, 'dummy')

    def __call__(self, tar):
        return tar

    def getExtension(self):
        return ''


'''
Callable class implementing the cipher interface (key, tar_to_be_cipherd),
but doing nothing.
'''
class CypherAes(ACypher):
    def __init__(self, password):
        ACypher.__init__(self, 'aes')
        if password == '':
            Error_Fatal("Error: The AES key is void. Check your ini file.")
        self.SALT = get_random_bytes(8)
        self.KEY = KDF.PBKDF2(password, self.SALT)
        self.password = password

    def __call__(self, tar):
        print("Cyphering with AES")
        nonce = get_random_bytes(16)
        ctr_aes = Counter.new(128, initial_value=int(binascii.hexlify(nonce), 16))
        cipher = AES.new(self.KEY, AES.MODE_CTR, counter=ctr_aes)
        return nonce + self.SALT + cipher.encrypt(tar)

    



'''
Callable class implementing the sending interface (archive_to_be_sent, file_extension),
saving the archive locally
'''
class SenderLocal():
    def __init__(self, dir_output):
        self.dir_out = dir_output
    
    def __call__(self, archive, name_tar):
        fullpath = os.path.join(self.dir_out, name_tar)
        print("Saving " + fullpath)
        try:
            with open(fullpath , "wb") as file_tar:
                file_tar.write(archive)
                return NO_ERROR
        except OSError as e:
            Error("{}\n{}\n".format(e.strerror, e.filename))
            return 1

    # Inits the provided db with relevant info
    def dbInit(self, connection):
        cmd = connection .cursor()
        cmd.execute(''' CREATE TABLE IF NOT EXISTS sender
            (type TEXT, dir_out TEXT)''')
        cmd.execute('SELECT type from sender LIMIT 0,1')
        type_sender = cmd.fetchone()
        if type_sender is None:
            cmd.execute('''INSERT INTO sender VALUES(?,?)''', ['local', self.dir_out])
        connection .commit()
        return NO_ERROR

'''
Callable class implementing the retrieving interface (archive, dir_output),
restoring the archive from a local directory
'''
class RetrieverLocal():
    def __init__(self, dir_input):
        self.__dir_intput = dir_input

    def __call__(self, name_tar):
        print("Fetching {}".format(name_tar))
        try:
            archive = b''
            with open(os.path.join(self.__dir_intput, name_tar), 'rb') as file_tar:
                archive = file_tar.read()
        except OSError as e:
            Error("{}\n{}\n".format(e.strerror, e.filename))
            return archive, 1
        return archive, NO_ERROR



'''
Class implementing an SFTP connexion
'''
class ConnectionSftp():
    '''
    @param config "host", "user", "password", "dir"
    '''
    def __init__(self, config):
        self.config = config
        self.__transport = paramiko.Transport((self.config["host"], self.config["port"]))      
        try:
            self.__transport.connect(username = self.config["user"], password = self.config["password"])
            self.__sftp = paramiko.SFTPClient.from_transport(self.__transport)
        except Exception as e:
            Error_Fatal(e.args)

    def getSftp(self):
        return self.__sftp

    def __del__(self):
        self.__sftp.close()
        self.__transport.close()


'''
Callable class implementing the sending interface (archive_to_be_sent, file_extension),
saving the archive to a SFTP server
'''
class SenderSftp():
    '''
    @param config "host", "user", "password", "dir"
    '''
    def __init__(self, config):
        warnings.simplefilter("ignore", cryptography.utils.CryptographyDeprecationWarning)  # mismatch between paramiko and crypto2.5
                                                                                            # shall be OK in net paramiko release.
        self.__connection = ConnectionSftp(config)
        self.__sftp = self.__connection.getSftp()
        self.__dir = config['dir']

    def __call__(self, archive, name_tar):
        config = self.__connection.config
        dest = self.__dir + "/" + name_tar # the separator is always /
        print("Sending to {}:{} > {}".format(config["host"], config["port"], dest))
        try:
            self.__sftp.putfo(BytesIO(archive), dest)
            return NO_ERROR
        except OSError as e:
            Error("{}\n{}\n".format(e.strerror, e.filename))
            return 1
        except Exception as e:
            Error(e.args)
            return 1

    # Inits the provided db with relevant info
    def dbInit(self, connection):
        cmd = connection .cursor()
        cmd.execute(''' CREATE TABLE IF NOT EXISTS sender
            (type TEXT, host TEXT, port INT, user TEXT, password TEXT, dir TEXT)''')
        cmd.execute('SELECT type from sender LIMIT 0,1')
        type_sender = cmd.fetchone()
        config = self.__connection.config
        if type_sender is None:
            cmd.execute('''INSERT INTO sender VALUES(?,?,?,?,?,?)''',
            ['sftp', config["host"], config["port"], config["user"], config["password"], self.__dir])
        connection .commit()
        return NO_ERROR



'''
Callable class implementing the retrieving interface (archive, dir_output),
restoring the archive from a sftp server
'''
class RetrieverSftp():
    '''
    @param config "host", "user", "password", "dir"
    '''
    def __init__(self, config):
        self.__connection = ConnectionSftp(config)
        self.__sftp = self.__connection.getSftp()
        self.__dir = config['dir']


    def __call__(self, name_tar):
        config = self.__connection.config
        src = self.__dir + "/" + name_tar # the separator is always /
        print("Fetching {} < {}:{}".format(src, config["host"], config["port"]))
        try:
            archive = b''
            with BytesIO() as buffer:
                self.__sftp.getfo(src, buffer)
                buffer.flush()
                archive = buffer.getvalue()
        except OSError as e:
            Error("{}\n{}\n".format(e.strerror, e.filename))
            return archive, 1
        return archive, NO_ERROR



'''
Main application
This class has operations with the same names as the commands, allowing to use the 'dispatch pattern'
'''
class Application():

    # Parses the config ini file and returns corresponding objects and properties
    def __ParseIniConfig(self, ini):
        config = configparser.ConfigParser()
        if os.path.isfile(ini):
            config.read(ini)
        else:
            config.read_string(ini)

        # get cipher
        if config['Tar']['ciphered'] == 'yes':
            cipher = CypherAes(config['Tar']['password'])
            decipher = DecipherAes(config['Tar']['password'])
        elif config['Tar']['ciphered'] == 'no':
            cipher = CypherDummy()
            decipher = DecypherDummy()
        else:
            Error_Fatal("\'cipher\' must be \'yes\' or \'no\'. Check your ini file.")
        # get sender
        if config['Repository']['type'] == 'local':
            sender = SenderLocal(config['Local']['dir'])
            retriever = RetrieverLocal(config['Local']['dir'])
        elif config['Repository']['type'] == 'sftp':
            conf_sftp = dict()
            conf_sftp["host"] = config["Sftp"]["host"]
            conf_sftp["port"] = int(config["Sftp"]["port"])
            conf_sftp["user"] = config["Sftp"]["user"]
            conf_sftp["password"] = config["Sftp"]["password"]
            conf_sftp["dir"] = config["Sftp"]["dir"]
            sender = SenderSftp(conf_sftp)
            retriever = RetrieverSftp(conf_sftp)
        else:
            Error_Fatal("Sender {} is not supported. Check your ini file.".format(config['Cloud']['access_cloud']))

        return {
            "sender": sender,
            "retriever": retriever,
            "cipher": cipher,
            "decipher": decipher,
            "dir_to_archive": config["Archive"]["directory"].replace("//","/").replace('\"',''),
            "exclude": config["Archive"]["exclude"],
            "size_tar": config["Tar"]["size_tar"],
            "name":config["Archive"]["name"]
        }

    # Compare the dir to archive with a previous state
    def __Compare(self, dir_archive, json_prev_state):

        # Sanity
        if not os.path.isdir(dir_archive):
            Error_Fatal("{} is not a directory. Check your ini file.".format(dir_archive))

        json_new_state = tempfile.gettempdir() + "/archiver-new.json"
        json_diff = tempfile.gettempdir() + "/diff.json"

        # new state of the source    
        cmd = GetExeName("scan_folder") + " --fast -d \"" + dir_archive +"\" -o \"" + json_new_state + "\""
        if os.system(cmd) != 0:
            sys.exit(-1)
        # comparison
        cmd = GetExeName("compare_folders") + " -j \"" + json_new_state + "\" -j \"" + json_prev_state + "\" -o " + json_diff
        if os.system(cmd) != 0:
            sys.exit(-1)

        return json_diff, json_new_state      


    # Creates the list of tar
    def __CreateListTar(self, files_to_archive, size_tar_max):
        list_tars = []
        files_in_tar = []
        size_files = 0
        for file_info in files_to_archive:
            size_files += file_info["size"]
            files_in_tar.append(file_info["path"])
            if size_files > size_tar_max:
                list_tars.append(files_in_tar)
                files_in_tar = []
                size_files = 0
        if len(files_in_tar) > 0:
            list_tars.append(files_in_tar)
        return list_tars

    # Creates a tar with the files
    def __Tar(self, name_tar, dir_root, list_files):        
        print("taring " + name_tar)
        try:
            with BytesIO() as buffer:
                with tarfile.open(mode="w:gz", fileobj=buffer, format=tarfile.PAX_FORMAT) as file_tar:
                    for filename in list_files:
                        file_tar.add(dir_root + "/" + filename)
                buffer.flush()
                return buffer.getvalue()
        except FileNotFoundError as e:
            Error_Fatal("{}\n{}".format(e.strerror, e.filename))
        

    # Creates a tar with the files
    def __Untar(self, buffer, destination):
        if not os.path.isdir(destination):
            Error_Fatal("{} is not a valid directory.".format(destination))

        print("Untaring")
        bytes_tar = BytesIO(buffer)
        try:
            with tarfile.open(mode="r:*", fileobj=bytes_tar) as file_tar:
                file_tar.extractall(destination)
        except tarfile.TarError as e:
            Error_Fatal("{}. Corrupted file or bad password?".format(e.args[0]))
        except OSError as e:
            Error_Fatal("{}\n{}\n".format(e.strerror, e.filename))

            

    # Archive the files identified from the diff
    def __Archive(self, config, file_diff, json_new_state, dry = False):

        # Open the JSONs and sanitize
        try:
            with open(file_diff, "r", encoding="utf-8") as file_json:
                diff = json.load(file_json)
            if(diff[JSON_KEY_GENERATOR] != "info.xtof.COMPARE_FOLDERS"):
                Error_Fatal("Invalid JSON file")
            with open(json_new_state, "r", encoding="utf-8") as file_json:
                source = json.load(file_json)
            if(source[JSON_KEY_GENERATOR] != "info.xtof.COMPARE_FOLDERS"):
                Error_Fatal("Invalid JSON file")
        except OSError as e:
            Error_Fatal("{}\n{}\n".format(e.strerror, e.filename))

        # Build the list of the files to be archived
        # reading those which could not be archived during previous session
        files_to_archive = self.__storage.getListFiles() # get the files that were not archived last run
        files_deleted = []
        for file in files_to_archive:
            path = os.path.join(config['dir_to_archive'], file["path"])
            if not os.path.isfile(path): # if the file was deleted since then
                files_deleted.append(file)
        for file in files_deleted:
            files_to_archive.remove(file)
            self.__storage.removeFiles([file["path"]])
        # adding the files resulting from the folder' state comparison
        if JSON_KEY_DIFFERENT in diff:
            for file in diff[JSON_KEY_DIFFERENT]:
                files_to_archive.append({
                    "path": file,
                    "size": int(source[JSON_KEY_FILES][file][JSON_KEY_SIZE]
                )})
        if JSON_KEY_UNIQUE_LEFT in diff:
            for file in diff[JSON_KEY_UNIQUE_LEFT]:
                files_to_archive.append({
                    "path": file,
                    "size": int(source[JSON_KEY_FILES][file][JSON_KEY_SIZE]
                )})
        if JSON_KEY_RENAMED in diff: # if the file has been renamed, it has to be archived again with its new name
            for hash, paths in diff[JSON_KEY_RENAMED].items():
                for file in paths[JSON_KEY_LEFT]:
                    files_to_archive.append({
                        "path": file,
                        "size": int(source[JSON_KEY_FILES][file][JSON_KEY_SIZE]
                    )})
        # exluding files matching the exclude regexp
        regexp_exlusion = config["exclude"]
        if not len(regexp_exlusion) == 0:
            regexp = re.compile(config["exclude"])
            files_to_exclude = []
            for file in files_to_archive:
                if not regexp.search(file["path"]) is None:
                    files_to_exclude.append(file)
            for file in files_to_exclude:
                files_to_archive.remove(file)
        # saving the files to archive into the database
        self.__storage.setListFiles(files_to_archive)
        nb_files_to_archive = len(files_to_archive)
        
        # Builds and sends the archives
        cipher = config["cipher"]
        send = config["sender"]
        self.__storage.setSender(send)
        self.__storage.setCypher(cipher)
        date_time = strftime("%Y%m%d-%H%M%S", localtime())
        size_max = 1024*1024*int(config["size_tar"])
        list_tar = self.__CreateListTar(files_to_archive, size_max)
        size_total = 0
        for idx, tar in enumerate(list_tar):
            print("{} files left to archive.".format(nb_files_to_archive))
            name_tar = "ARCHIVE_{}_".format(config["name"]) + date_time + "_{0:06d}.tar.gz".format(idx) + cipher.getExtension()
            archive = self.__Tar(name_tar, config['dir_to_archive'], tar)
            archive = cipher(archive)
            if dry == False:            
                if send(archive, name_tar) == NO_ERROR:
                    self.__storage.removeFiles(tar)
                    self.__storage.addTar(name_tar)
                    nb_files_to_archive = nb_files_to_archive - len(tar)
                    size_total += len(archive)
            else:
                print("Dry run: the archive is not sent.")
                nb_files_to_archive = nb_files_to_archive - len(tar)
                size_total += len(archive)
        
        return size_total


    def __init__(self):

        # parse the arguments
        parser = argparse.ArgumentParser(
            description="Archives files on a distant server.",
            usage=''' pyArchiver <command> [<options>]

The possible commands are:
    init        Initializes an empty ini file to configure your archive.
    start       Starts a new archive, following instructions from an ini file.
    resume      Resumes an archiving process.
    restore     Restores an archive.
    decipher    Deciphers archive files in a given folder.
    about       Prints info about this program.
''')
        parser.add_argument("command", help="subcommand to run")
        args = parser.parse_args(os.sys.argv[1:2])    # only parsing the command!
        
        # call the operation named as the command ("dispatch pattern")
        if not hasattr(self, args.command):
            Error_Fatal("Unrecognized command.")
        getattr(self, args.command)()


    '''
    Executes the init command.
    '''
    def init(self):
        # Parse the options
        parser = argparse.ArgumentParser(
            description="Initialise an empty .ini file to configure your archive.")
        parser.add_argument("ini", help="configuration file to be created.")
        args = parser.parse_args(os.sys.argv[2:])

        # Creating the ini file
        str_ini = """
; pyArchiver configuration
[Id]
id_ini=pyArchiver
version_ini=1

; Archive description
[Archive]
; Directory to be archived
directory=
; Name of the archive. Default: directory's name
name=
; Regular expression to exclude files and folders matching the pattern (python' style)
exclude=

; Tar files description
[Tar]
; tar file max size in MB
size_tar=512
; yes / no
ciphered=no
; a password is required if ciphered=yes
password=

; Repository
[Repository]
; local or sftp
type=

; LOCAL parameters
; The archiving files are saved locally
[Local]
; output directory
dir=

; SFTP parameters
; The archiving files are pushed on a distant server via sftp
[Sftp]
; distant server
host=
; connection port
port=22
; user name
user=
; user's password
password=
; directory on server
dir=
"""
        with open(args.ini,"wt") as file_ini:
            file_ini.write(str_ini)



    '''
    Executes the start command.
    args.option is the .ini filename to be used as configuration
    '''
    def start(self):

        # Parse the options
        parser = argparse.ArgumentParser(
            description="Starts a new archive.")
        parser.add_argument("ini", help="Configuration of the archive")
        parser.add_argument("--dry-run", dest="dry", action='store_true', default=False, help="Test mode. The archives will be produced in memory but won't be sent to the repository.")
        args = parser.parse_args(os.sys.argv[2:])

        ### Sanity
        if not os.path.isfile(args.ini):
            Error_Fatal(args.ini + " does not exists.")
        
        ### Parsing the ini file
        config = self.__ParseIniConfig(args.ini)
        file_db = "{}.archive".format(config["name"])
        if os.path.isfile(file_db):
            Error_Fatal("{} already exists.".format(file_db))
        dir_to_archive = config["dir_to_archive"]

        ### Creation of an empty json file as "previous state"
        json_prev_state = tempfile.gettempdir() + "/archiver-old.json"
        with open(json_prev_state, "w", encoding="utf-8") as file_json:
            file_json.write(CreateEmptyJson(dir_to_archive))

        # Compare folder states
        file_diff, json_new_state = self.__Compare(dir_to_archive, json_prev_state)
        
        # Initiate configuration
        self.__storage = Storage("{}.archive".format(config["name"]))
        self.__storage.setConfig(args.ini)
        self.__storage.setState(json_new_state)

        # Archive the files
        size = self.__Archive(config, file_diff, json_new_state, args.dry)

        print("{} bytes saved on repository.".format(size))


    
    '''
    Executes the resume command.
    args.option:
        archive_file
    '''
    def resume(self):

        ### Parse the options
        parser = argparse.ArgumentParser(
            description="Resumes an archive.")
        parser.add_argument("archive", help="File describing the archive.")
        parser.add_argument("--dry-run", dest="dry", action='store_true', default=False, help="Test mode. The archives will be produced in memory but won't be sent to the repository.")
        args = parser.parse_args(os.sys.argv[2:])

        ### Sanity
        if not os.path.isfile(args.archive):
            Error_Fatal(args.archive + " does not exists.")

        ### Getting the conf back
        self.__storage = Storage(args.archive)
        config = self.__ParseIniConfig(self.__storage.getConfig())
        dir_to_archive = config["dir_to_archive"]

        ### Creation of an empty json file as "previous state"
        json = self.__storage.getState()
        json_prev_state = os.path.join(tempfile.gettempdir(), "archiver-old.json")
        with open(json_prev_state, "wb") as file_json:
            file_json.write(json)
        
        # Compare folder states
        file_diff, json_new_state = self.__Compare(dir_to_archive, json_prev_state)
        self.__storage.setState(json_new_state)
        
        # Archive the files
        size = self.__Archive(config, file_diff, json_new_state, args.dry)

        print("{} bytes saved on repository.".format(size))



        
    '''
    Executes the restore command.
    args.option:
        archive file
        destination were to restore the files
    '''
    def restore(self):

        ### Parse the options
        parser = argparse.ArgumentParser(
            description="Restores an archive.")
        parser.add_argument("archive", help="File describing the archive.")
        parser.add_argument("destination", help="Directory where the files will be restored.")
        args = parser.parse_args(os.sys.argv[2:])

        ### Sanity
        if not os.path.isfile(args.archive):
            Error_Fatal(args.archive + " does not exists.")
        if not os.path.isdir(args.destination):
            Error_Fatal(args.destination + " does not exists.")

        ### Restores the files
        self.__storage = Storage(args.archive)
        ini = self.__storage.getConfig()
        config = self.__ParseIniConfig(ini)
        fetch = config["retriever"]
        decipher = config["decipher"]
        trove = self.__storage.getArchives()
        print("{} tar files will be fetched and extracted.".format(len(trove)))
        for archive in trove:
            name_archive = archive[0]
            tar, error = fetch(name_archive)
            if error == NO_ERROR:
                tar = decipher(tar)
                self.__Untar(tar, args.destination)

    

    '''
    Executes the decipher command.
    args.option:
        source_dir output_dir password
    '''
    def decipher(self):
        ### Parse the options
        parser = argparse.ArgumentParser(
            description="Restores an encrypted archive from a local directory.")
        parser.add_argument("source", help="Directory hosting the encrypted archive.")
        parser.add_argument("destination", help="Directory where the files will be restored.")
        parser.add_argument("password", help="Password required to decipher the archive.")
        args = parser.parse_args(os.sys.argv[2:])

        ### Sanity
        if not os.path.isdir(args.source):
            Error_Fatal(args.source + " does not exists.")
        if not os.path.isdir(args.destination):
            Error_Fatal(args.destination + " does not exists.")
        
        ### List the files
        decipher = DecipherAes(args.password)
        fetch = RetrieverLocal(args.source)
        archives = list()
        for file in os.listdir(args.source):
            if file.endswith(decipher.getExtension()):
                archives.append(file)
        archives = sorted(archives)
        
        ### Restore the files
        for archive in archives:
            tar = fetch(archive)
            tar = decipher(tar)
            self.__Untar(tar, args.destination)




    def about(self):
        print('''Copyright (C) 2019 Christophe Meneboeuf <christophe@xtof.info>.
        
This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.
''')


##########################    

if __name__ == '__main__':
    
    Application()
    PrintErrors()
    sys.exit(len(Errors))