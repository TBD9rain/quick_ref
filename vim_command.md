# Instruction

- `[N]` means optional number, default is 1
- `{object}` means specific object
- `<Up>` means 'up' key on keyboard
- `<Ctrl>-I` means 'ctrl' key plus 'i' or 'I' key
- other characters in `code block` means corresponding keys on keyboard

|Mode Abreviation   |Mode               |
|:---               |:---               |
|N                  |Normal             |
|I                  |Insert             |
|VB                 |Block Visual       |
|VL                 |Line Visual        |
|R                  |Replace            |
|X                  |Complete           |
|RR                 |Register Record    |
|PS                 |Pattern Substitute |

# General Commands

|Command                |Mode                       |Description                                        |
|:---                   |:---                       |:---                                               |
|`:help`                |N                          |open help file                                     |
|`<Esc>`                |I, V, R $\rightarrow$ N    |enter normal mode                                  |
|`:{command}`           |N                          |command in command line                            |
|`:!{command}`          |N                          |execute external command, e.g., complie c file     |
|`:<Up>`                |N                          |last command in command line                       |
|`<Ctrl>-]`             |N                          |jump into link                                     |
|`<Ctrl>-O`             |N                          |jump back                                          |
|`<Ctrl>-I`             |N                          |jump foward                                        |
|`:w[q]`                |N                          |save [and exit vim]                                |
|`sa[veas] {file_path}` |N                          |save as \<file\_path\>                             |
|`:q!`                  |N                          |force exit without save                            |

# Cursor Moving Commands

|Command        |Mode   |Description                                |
|:---           |:---   |:---                                       |
|`[N]h`         |N      |left N characters                          |
|`[N]l`         |N      |right N characters                         |
|`[N]k`         |N      |up N lines                                 |
|`[N]j`         |N      |down N lines                               |
|`[N]w`         |N      |forward to Nth word head                   |
|`[N]W`         |N      |forward to Nth blank-separated word head   |
|`[N]b`         |N      |backward to Nth word head                  |
|`[N]B`         |N      |backward to Nth blank-separated word head  |
|`[N]e`         |N      |forward to Nth word end                    |
|`[N]E`         |N      |forward to Nth blank-separated word end    |
|`[N]f{char}`   |N      |to the Nth {char} to the right             |
|`[N]F{char}`   |N      |to the Nth {char} to the left              |
|`^`            |N      |to first non-blank character in the line   |
|`0`            |N      |to first character in the line             |
|`[N]$`         |N      |to last character in the (N-1) below line  |
|`[N]gg`        |N      |to line N, default: first line             |
|`[N]G`         |N      |to line N, default: last line              |
|`:[N]`         |N      |to line N                                  |

# Editing Commands in Normal Mode

|Command        |Mode               |Description                                                                            |
|:---           |:---               |:---                                                                                   |
|`[N]i{text}`   |N $\rightarrow$ I  |enter insert mode, insert {text} before the cursor for N times                         |
|`[N]I{text}`   |N $\rightarrow$ I  |enter insert mode, insert {text} before the first non-blank character for N times      |
|`[N]a{text}`   |N $\rightarrow$ I  |enter insert mode, append {text} after the cursor for N times                          |
|`[N]A{text}`   |N $\rightarrow$ I  |enter insert mode, append {text} after the last character in the line for N times      |
|`[N]o`         |N $\rightarrow$ I  |enter insert mode, open N new lines below this line                                    |
|`[N]O`         |N $\rightarrow$ I  |enter insert mode, open N new lines above this line                                    |
|`[N]R{text}`   |N $\rightarrow$ R  |enter replace mode, replace text with {text} for N times                               |
|`[N]u`         |N                  |undo last N modifications                                                              |
|`[N]<Ctrl>-R`  |N                  |redo last N undone modifications                                                       |
|`[N]x`         |N                  |delete N characters at and after the cursor                                            |
|`[N]d{motion}` |N                  |delete texts selected by {motion}                                                      |
|`[N]dd`        |N                  |delete N lines                                                                         |
|`[N]D`         |N                  |delete to the end of the line and (N-1) more lines                                     |
|`[N]r{char}`   |N                  |replace N characters at and after the cursor with {char}                               |
|`[N]c{motion}` |N $\rightarrow$ I  |delete texts selected by {motion} and enter insert mode                                |
|`[N]cc`        |N $\rightarrow$ I  |delete N lines and enter insert mode                                                   |
|`[N]C`         |N $\rightarrow$ I  |delete to the end of the line and (N-1) more lines and enter insert mode               |
|`[N]~`         |N                  |switch case for N characters at and after the cursor                                   |
|`[N]<Ctrl>-A`  |N                  |add N to the number at or after the cursor                                             |
|`[N]<Ctrl>-X`  |N                  |reduce N to the number at or after the cursor                                          |
|`[N]>>`        |N                  |add 1 shiftwidth indent at heads of N lines                                            |
|`[N]<<`        |N                  |reduce 1 shiftwidth indent at heads of N lines                                         |
|`[N]y{motion}` |N                  |copy text selected by N {motion} into default register                                 |
|`[N]yy`        |N                  |copy N lines into default register                                                     |
|`[N]p`         |N                  |paste text in default register after the cursor for N times                            |
|`[N]P`         |N                  |paste text in default register before the cursor for N times                           |

# Commands for Visual Mode

|Command        |Mode                   |Description                                                                            |
|:--            |:---                   |:---                                                                                   |
|`v`            |N $\rightarrow$ V      |enter visual mode                                                                      |
|`<Ctrl>-V`     |N $\rightarrow$ VB     |enter visual mode blockwise                                                            |  
|`V`            |N $\rightarrow$ VL     |enter visual mode linewise                                                             | 
|`[N]I`         |VB $\rightarrow$ I     |enter insert mode, insert {text} before each selected lines for N times                |
|`[N]A`         |VB $\rightarrow$ I     |enter insert mode, append {text} after each selected lines for N times                 |
|`x` or `d`     |V, VB, VL              |delete selected texts                                                                  |
|`r{char}`      |V, VB, VL              |replace selected texts with {char}                                                     |
|`c`            |VB $\rightarrow$ I     |delete selected texts, enter insert mode and insert same {text} for each selecetd line |
|`y`            |V, VB, VL              |copy selected texts                                                                    |

# Commands in Insert Mode

|Command                    |Mode       |Description                                                                            |
|:--                        |:---       |:---                                                                                   |
|`<Up>`                     |I          |move cursor up                                                                         |
|`<Down>`                   |I          |move cursor down                                                                       |
|`<Left>`                   |I          |move cursor left                                                                       |
|`<Right>`                  |I          |move cursor right                                                                      |
|`<Ctrl>-T`                 |I          |add 1 shiftwidth indent at head of the line                                            |
|`<Ctrl>-D`                 |I          |reduce 1 shiftwidth indent at head of the line                                         |
|`<Ctrl>-R{reg}`            |I          |insert texts in the {reg} register, e.g., `<Ctrl>-R%` insert current file path         |
|`<Ctrl>-R<Ctrl>-R{reg}`    |I          |insert raw texts in the {reg} register                                                 |
|`<Ctrl>-V{key}`            |I          |insert original meanings of keyboard keys, e.g., `<Ctrl>-V<Delete>` insert '\<Del\>'   |
|`<Ctrl>-Y`                 |I          |insert character above the cursor                                                      |
|`<Ctrl>-E`                 |I          |insert character below the cursor                                                      |

# Commands for Completion Mode

|Command        |Mode                   |Description                                                                    |
|:--            |:---                   |:---                                                                           |
|`<Ctrl>-P`     |I, R $\rightarrow$ X   |enter complete mode, insert previous match of identifier before the cusor      |
|`<Ctrl>-N`     |I, R $\rightarrow$ X   |enter complete mode, insert next match of identifier before the cusor          |
|`<Ctrl>-X`     |I, R $\rightarrow$ X   |enter complete mode, and view completion selections                            |
|`<Ctrl>-Y`     |X $\rightarrow$ I, R   |determine match item and return to original mode                               |
|`<Ctrl>-E`     |X $\rightarrow$ I, R   |reserve original texts and return to original mode                             |
|`<Ctrl>-F`     |X                      |file name completion                                                           |
|`<Ctrl>-P`     |X                      |keyword local compeltion; previous match item wihle selecting                  |
|`<Ctrl>-N`     |X                      |keyword local compeltion; next match item wihle selecting                      |

# Commands about Register

|Command                |Mode   |Description                                                            |
|:--                    |:---   |:---                                                                   |
|`:reg[ister]`          |N      |show contents in all registers                                         |
|`:reg[ister]{reg}`     |N      |show contents in register {reg}                                        |
|`"{reg}`               |N      |set register {reg} for next delete, copy or paste                      |
|`q{a-z}` or `q{A-Z}`   |N      |start to record keyboard input into register {a-z}                     |
|`q`                    |N      |stop regiter record                                                    |
|`[N]@{a-z}`            |N      |execute contents in register {a-z} like keyboard input for N times     |

Use command **`:help registers`** in vim to view descriptions for all registers.

# Pattern Search Commands

|Command                    |Mode   |Description                                                                        |
|:--                        |:---   |:---                                                                               |
|`[N]/{pattern}[/[offset]]` |N      |search forward for the Nth string satisfying {pattern} and go [offset] lines down  |
|`[N]/`                     |N      |search forward for the Nth string with last {pattern} and last [offset]            |
|`[N]//[offset]`            |N      |search forward for the Nth string with last {pattern} and new [offset]             |
|`[N]?{pattern}[?[offset]]` |N      |search backward for the Nth string satisfying {pattern} and go [offset] lines down |
|`[N]/`                     |N      |search backward for the Nth string with last {pattern} and last [offset]           |
|`[N]//[offset]`            |N      |search backward for the Nth string with last {pattern} and new [offset]            |
|`[N]*`                     |N      |search forward for the Nth string same as the identifier nearest to cursor         |
|`[N]#`                     |N      |search backward for the Nth string same as the identifier nearest to cursor        |
|`[N]n`                     |N      |repeat last search for N times                                                     |
|`[N]N`                     |N      |repeat last search in opposite direction for N times                               |

Use command **`:help pattern`** in vim to view available pattern expressions.

# Pattern Substitute Commands

```
:[range]s[ubstitute]/{pattern}/{string}/[flag]
```

Enter PS mode and substitute {pattern} pattern with {string} string in \[range\].
Replace operation is controlled by \[flag\].

\[range\]:
`.`, current line;
`66`, line 66;
`78,+5`, line 78 to line 83;
`%` or `1,$`, whole file;
`{pattern 1},{pattern 2}`, string satisfying {pattern 1} to string satisfying {pattern 2};
default, selected area or current line.

\[flag\]:
g, all matchs in the same line, otherwise only the first match will be substituted;
c, need manual confirmation for each substitute;
i, ignore case for {pattern};
I, don't ignore case for {pattern}.

Instead of `/`, other characters cloud be used as delimiter pattern substitute command, 
except alphanumeric characters, `\`, `"`, `|`, or `#`(for Vim9).

```
:[range]s[ubstitute] [flag]
```
or
```
:[range]&[&] [flag]
```

Repeat last substitute command with new [flag].

Use command `:help substitute` in vim to view more information.
Use command `:help pattern` in vim to view available pattern expressions.

# Tab Page Commands

|Command                    |Mode   |Description                                                        |
|:--                        |:---   |:---                                                               |
|`:tabnew {file_path}`      |N      |open a tab page for an existing file or a new file                 |
|`gT`                       |N      |switch to the previous tabpage                                     |
|`gt`                       |N      |switch to the next tabpage                                         |
|`:tab[close]`              |N      |close current tab page                                             |
|`:tabo[nly]`               |N      |close all tab pages except current page                            |
|`:tabm[ove]`               |N      |move current tab page to after page N, or use **mouse** to drag    |

# Fold Commands

|Command        |Mode       |Description                                |
|:--            |:---       |:---                                       |
|`zf{motion}`   |N          |create 1 fold                              |
|`zf`           |V, VB, VL  |create 1 fold                              |
|`zd`           |N          |delete 1 fold at the cursor                |
|`zD`           |N          |delete all folds at the cursor             |
|`zE`           |N          |delete all folds in the window             |
|`zo`           |N          |open 1 fold at the cursor                  |
|`zO`           |N          |open all folds at the cursor recursively   |
|`zc`           |N          |close 1 fold at the cursor                 |
|`zC`           |N          |close all folds at the cursor recursively  |
|`zr`           |N          |reduce folding                             |
|`zR`           |N          |open all folds in current window           |
|`zm`           |N          |increase folding                           |
|`zM`           |N          |Close all folds in current window          |

