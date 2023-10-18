# Introduction

This is a quick reference for Git commands in **git & github**.

To get help in Git, type `git help <operation>` or `git <operation> --help` in command line

For more info in Git, visit [Pro Git](https://git-scm.com/book/en/v2) or [Github doc](https://docs.github.com/en).


# Install Git

Visit [Git download](https://git-scm.com/downloads) to get Git installation package.


# How to Use Git

For windows:
- **CMD or Powershell**
- **Git bash**
- Git GUI
- Third party software

The usage of **Git commands** in windows command line is the focus of this ref.

# Configure Git

There are three Git config files in different levels and different disk locations to configure Git. 
The configurations and options within installation process can be modified in config files. 
Three Git config files windows 10:

1. system config file works for the whole OS: 
    - \<git directory\>/ect/gitconfig
2. global config file works for the current login user:
    - \<user directory\>/.gitconfig
3. local config file works for the specific repository directory:
    - \<repository directory\>/.git/config

**The local config covers global config, and global config covers general config.**

For more info, type `git config --help`.

## List configurations 

Use the following command to display git configures. Add `--show-origin` option to display origin config file as well.

```
git config --list
```

## Set or unset variables

`git config --add <var>` set the variable in local config file where `--local` is optional. 

`git config --unset <var>` unset the variable in local config file. 

Add option *`--local`*, **`--global`**, or ***`--system`*** to operate in a specific level. 

Configure user name and email in global config file (usually used) with following command:

```
git config --global user.name "USER NAME"
git config --global user.email "MYEAMIAL@MINE.ME"
```

Additionally, the git config file can be edited with editor.

For all available configurations, type `git config --help` to view.


# Git Work Flow

```mermaid
flowchart RL
    local[("local directory")]

    other[("other repository")]

    cached[("cached area")]

    committed[("local repository")]

    remote[("remote repository")]

    cached      ==>|"commit"| committed
    local       ==>|"init"| committed
    other       ==>|"clone"| committed
    committed   ==>|"push"| remote
    remote      ==>|"pull"| committed

    untracked["untracked
        files"]

    modified["modified
        files"]

    updated["updated
        files"]

    untracked   -->|"add"| cached
    modified    -->|"add"| cached
    remote      -->|"fetch"| updated
    updated     -->|"merge"| modified
```

<!--
```mermaid
sequenceDiagram
    participant untracked files
    participant cached area
    participant modified files
    participant updated files
    participant local repository
    participant remote repository
    participant web repository
    participant local directory

    rect rgb(255, 205, 178)
        Note right of local repository                  : create local repository
        web repository      ->>local repository         : clone
        local directory     ->>local repository         : init
    end

    rect rgb(255, 180, 162)
        Note right of untracked files                   : track & untrack files
        untracked files     ->>cached area              : add
        cached area         ->>untracked files          : rm --cached
    end

    rect rgb(229, 152, 155)
        Note right of cached area                       : modify tracked files
        modified files      ->>cached area              : reset --staged (discard)
        modified files      ->>cached area              : add (accept)
    end

    rect rgb(181, 131, 141)
        Note right of cached area                       : archive files
        cached area         ->>local repository         : commit
        local repository    ->>remote repository        : push
    end

    rect rgb(109, 104, 117)
        Note right of local repository                  : update local repository
        remote repository   ->>local repository         : pull
    end

    rect rgb(109, 104, 117)
        Note over modified files, local repository      : download updated files and merge with local files
        remote repository   ->>updated files            : fetch
        updated files       ->>modified files           : merge
        modified files      ->>cached area              : add
    end

    rect rgb(181, 131, 141)
        Note right of cached area                       : achive files
        cached area         ->>local repository         : commit
        local repository    ->>remote repository        : push
    end
```
-->


# Local Repository

## Check local repository status

To check the status of local git repository, use the following command.
```
git status
```

## Initialize a repository

### Initialize a local directory

The following commands initialize a local working directory into a Git repository.
```
cd <working_directory>
git init
```

### Clone an existing repository

The fllowing command clone a existing repository 
from the internet or a local path 
and make a new working directory with named as the repository.
```
git clone <repository_path>
```

## Delete local repository

To delete a git local repository, directly delete `.git` directory by following commands or by
manual operations.
```
cd <target_directory>
rm -rf .git
```

## Ignore specific files

To ignore specific files while checking git status, add a file named `.gitignore` in local
repository directory.

For info about file ignorance method, check [github page](https://github.com/github/gitignore) 
or 
[Pro git](https://git-scm.com/book/en/v2/Git-Basics-Recording-Changes-to-the-Repository).


## Record files

### Add new files to cached area

To add current version of new files or modified files in the working directory to cached area, 
use the following command.
```
git add <file>
```


### Commit files to local repository

To commit files to local repository and save tracked files, use the following command.
```
git commit
```
After enter this command, a default editor will pop up and waits for a commit message.
Without a commit message, commit will fail.


## Recover files

### Remove added files

To move the **file** from cached area to working directory, use the following command.
```
git rm --cached <file>
```


### Discard changes in working directory

The following commands will dicard changes of the file in working directory. 
Both commands will also reload the verison of the file in the search order of: 
1. **cached area**
2. **last commit**
```
git restore <modified_file>
```
OR
```
git checkout -- <file>
```


### Discard changes in cached area

The following commands will move **changes** of the file from cached area to working directory. 
```
git restore --staged <modified_file>
```
OR
```
git reset HEAD <file>
```

## Compare files

To display changes between working directory and the last commit:
```
git diff
```

To display changes between cached area and the last commit:
```
git diff --cached
```


## Remove files

To remove a committed file from next commit and working directory:
```
git rm <file>
```

The above command equals to
```
rm <file>
git add <file>
```


# Commit management

## View commit history

To view commit history:
```
git log
```

The above command can be run with following options to show different information.
|Option             |Description                                    |
|:---               |:---                                           |
|`--graph`          |show branch history with graphic description   |
|`-p`               |show differences introduced by each commit     |
|`--shortstat`      |show abbreviated stats for each commit         |
|`--stat`           |shorten `--stat` infos                         |
|`--name-only`      |show names of changed files                    |
|`--name-status`    |show changes of changed files                  |
|`--pretty`         |show commits with alternate format             |

To limit output, use following options:
|Option                     |Description                                        |
|:---                       |:---                                               |
|`-[N]`                     |only last N commits                                |
|`--since` or `--after`     |only commits after the specific date               |
|`--until` or `--before`    |only commits before the specific date              |
|`--grep`                   |only commits with messages containing the string   |
|`-S`                       |only commits changing code matching the string     |
|`--author`                 |only commits with matched author                   |
|`committer`                |only commits with matched committer                |


## List branches
To view local branches:
```
git branch
```
To view merged or unmerged branches add option `--merged` or `--no-merged`.

To view remote branches of all remote repositories:
```
git branch -r
```

To view remote branches' tracking information:
```
git branch -vv
```


## Branch modifications
To create a new branch:
```
git branch <branch>
```

To rename the current branch:
```
git branch -m <new_branch_name>
```

To delete a branch:
```
git branch -d <branch>
```
Replace `-d` with `-D` to forcibly delete a branch which hasn't been merge to other branch.


## Checkout branches
To checkout an existing branch (move `HEAD` pointer to the branch):
```
git checkout <branch>
```

To create a new branch and checkout it immediately:
```
git checkout -b <branch>
```


# Remote Repository

## Check remote path

To view aliases of remote repositories configured for local repository:
```
git remote
```

To display remote repositories and associated URLs:
```
git remote -v
```

To view details of a remote repository:
```
git remote show <remote>
```


## Modify remote repository configs

To add a remote repository:
```
git remote add <remote> <url>
```

To rename a remote repository:
```
git remote rename <old_name> <new_name>
```

To change the URL of a remote repository:
```
git remote set-url <remote> <new_url>
```

To remove a remote repository:
```
git remote remove <remote>
```


## Push
```
git push <remote> <branch>
```


## Fetch
```
git fetch <remote>
```


## Pull
```
git pull <remote> <branch>
```


# Tagging
One commit can hold multiple tags.
No repeative tags are allowed.


## Local tagging
To view existing tags:
```
git tag
```

To list existing tags with match string, where `-l` is as the same as `-list`: 
```
git tag -l <string>
```

To add a tag to specific commit: 
```
git tag <tag> <commit>
```
If \<commit\> is not given, the target commit is the last commit.

To add a tag and annotations to specific commit:
```
git tag -a <tag> <commit>
```
If \<commit\> is not given, the target commit is the last commit.
After execute the above command, the editor will pop up for annotating.

To delete a tag:
```
git tag -d <tag>
```


## Remote tagging
To share local a specific tag to remote repository:
```
git push <remote> <tag>
```

To share all local tags to remote repository:
```
git push <remote> --tags
```

To delete a specific tag from remote repository:
```
git push <remote> --delete <tag>
```


