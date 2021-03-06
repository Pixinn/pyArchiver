# What is pyArchiver?

## *pyArchiver* is an **archiving** software.

Its main purpose is to push your most precious data on a distant server in order to achieve **distant** and possibly **cold** storage. In case of a catastrophic event destroying your data and your local backups, it will retrieve those archive and help mitigating your loss.

It is suitable to be used with cold storage providers only accepting one-way incoming commands.

## *pyArchiver* **is not a backuping software**.

Backuping and archiving do not serve the same purpose:

* A backup is intended to provide a *quick* mean of recovering data that is currently in use or was recently used.
* An archive is intended to store *final* set of data for a very long period of time. Typically, archives contain data that are not actively modified.

Backups and archives are, of course, not mutually exclusive.

## Services offered

 Bearing that *pyArchiver* is for archiving and not backuping, it offers:

* Incremental archiving
  * Only new and modified data is sent to the server
* Standard file formats and protocol support
  * If you do not encrypt your data, you shall be able to restore an archive without resorting to *pyArchiver*
* Optional encrytion
  * Do you trust your cloud provider?
* Versionning **is not** supported
  * It is designed to restore your archives as a whole data-set, faithfull to its latest state
* Deleted files will remain in the archive and will be restored
    * But why would you remove files from your precious trove of archives?


## Limitation

Most of the client-side work is done in memory. This is faster and do not write too much on SDDs in case of huge archives.
Thus you have to get around twice the amount of RAM than the biggest (single) file to archive. If this is too inconvenient, the script can be easily modified to work on disk.

# Get the binaries

Pre-built binary packages are available to download :
https://github.com/Pixinn/pyArchiver/releases/

# How to use pyArchiver

>pyArchiver \<command> [\<options>]

For each command you can type pyArchiver.py command --help

## init

Initialises an empty ini file to configure your archive.

>pyArchiver init \<ini_file>

All the relevant instructions are written in the *ini_file* itself.

## start

Starts a new archive, following instructions from an ini file. It will sends your archive to the provided server and produce a *.archive* file.

>pyArchiver start \<ini_file>

The *.archive* file will contain all the information necessary to resume or restore the archive afterwards. The *.ini* file can be discarded.

**PLEASE NOTE** that the *.archive* file contains the password used to cipher the files plus all the informations that are necessary to connect to your cloud provider. Do not store this file on an unprotected location.

## resume

Resumes an archiving process. If your connection was interrupted, it will gracefully send any missing file. It will also send any new file or file that was modified since the last execution of a *start* or *resume* command.

>pyArchiver resume \<archive_file>

## restore

Restores an archive. The files will be on the same state they had the last time *start* or *resume* were run. Any deleted files will also be restored.

>pyArchiver restore \<archive_file> \<destination>

## decipher

Can decipher the encrypted archived files even if the .archive file is not available. Those files have to be manually downloaded from your storage provider before being deciphered.

>pyArchiver decrypt \<archive_file> \<destination> \<password>

## delete

Deletes the files on the distant storage. Caution, this command cannot be undone.

>pyArchiver delete \<archive_file>

## update

Updates the archive file if was generated by an older version of pyArchiver.

>pyArchiver update \<archive_file>

## about

Some basic information about the program.


# Using the Python script

pyArchiver is written in Python. If you are more confortable calling the script that a prepackaged binaries, read the instructions below.

## Prerequistes

* The main script, pyArchiver.py, requires Python 3.6+
* some modules have to be installed using *pip*
    * paramiko>=2.4.2
    * pycryptodome>=3.7.3
    * configparser>=3.7.4

    > pip3 install paramiko pycryptodome configparser xxhash
    
You also need two programs: *scan_folder* and *compare_folder*. Here are links to download binaries for your platform of choice:

    * [Windows](https://pub.xtof.info/compare_folders/compare_folders_win.zip)
    * [Macos](https://pub.xtof.info/compare_folders/compare_folders_macos.zip)
    * [Debian (Ubuntu, etc)](https://pub.xtof.info/compare_folders/compare_folders_debian.zip)

If you want to **build** them yourself, their source code can be downloaded from [GitHub](https://www.github.com/Pixinn/libCompare). The build instructions are in the same location.
