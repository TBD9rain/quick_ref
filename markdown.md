This is a markdown syntax quick reference for github docs.

# Heading

There are 6 header levles as following:

# Heading level 1

## Heading level 2

### Heading level 3

#### Heading level 4

##### Heading level 5

###### Heading level 6


# Paragraph break

Use a blank line to break two paragraphs. 


# Text Decoration

|Description        |Syntax                     |Rendered                   |
|:---               |:---                       |:---                       |
|Bold               |`**Text**`                 |**Text**                   |
|Italic             |`*Text*`                   |*Text*                     |
|Bold and Italic    |`***Text***`               |***Text***                 |
|Crossed            |`~~Text~~`                 |~~Text~~                   |
|Subscript          |`Text<sub>subscript</sub>` |Text<sub>subscript</sub>   |
|Supscript          |`Text<sub>supscript</sub>` |Text<sub>supscript</sub>   |


# List

## Unordered List

Use `*`, `+`, or `-` to create an unordered list.

- List A, item 1
    - List A, item 1.1
        - List A, item 1.1.1
+ List B, item 1
    + List B, item 1.1
    + List B, item 1.2
* List C, item 1

## Ordered List

Use a number followed by a `.` to create an ordered list.

1. list item 1
    1. list item 1.1
2. list item 2
3. list item 3
    1. list itme 3.1

## Task List

Use `- [ ]` to create a task list.
Use `- [x]` to create a completed task list.

- [ ] task 1.
- [x] task 2.
- [ ] task 3.


# Link

## Hyperlink

Use `<hyperlink>` to make it clickable.
<https://markdown.com.cn/>

Use `[hyperlink_name](hyperlink "hovering_name")` to insert a hyperlink.
[Markdown](https://markdown.com.cn/ "Markdown Web in Chinese")

Hyperlink element can be decorated:
- ***[Markdown](https://markdown.com.cn/ "Markdown Web in Chinese")***
- **[Markdown](https://markdown.com.cn/)**
- *<https://markdown.com.cn/>*

## Link in Content (NOT available in markdown-preview.nvim)

Use `[link_name] [link_identifier]` to create a link starting point.
`link_identifier` could be consisted of letters, digits, spcace, and punctuation marks.
[tunnel] [tunnel1]

random text.

Use `[link_identifier]:` plus at least one space to create a link destination.
[tunnel1]: destination of tunnel1.

# Footnote

Use `[^footnote_identifier]` to create a footnote.
Use `[^footnote_identifier]: ` to create corresponding footnote text.
The location of footnote text in context **doesn't affect** the apperance location.

A footnote example[^1].

[^1]: footnote text example.


# Image

Use `![image_caption](image_link "hovering_name")` to insert an image.
Use `[![image_caption](image_link "hovering_name")](hyper_link)` to insert an image with a hyperlink.

![image example](https://markdown.com.cn/assets/img/philly-magic-garden.9c0b4415.jpg)

The above image is from [markdown](https://markdown.com.cn/basic-syntax/images.html)


# Reference

Use `>` to begin a reference line.
Reference can include other elements.
Reference can be nested in another reference.

> Do more than it can be done --Lingwei
> 
> **However**
>> Don't do too more -- Lingwei


# Split Line

Use **three** `*`, `-`, or `_` in a single line to insert a split line:

---

# Code

## Code in Line

Use one `` ` `` **pair** to wrap `code words` or `code phrases`.

Use two `` ` `` **pair** to wrap ``code `words` with backtick``.

## Code Block

Use three `` ` `` or `~` to create code block.

```
int main{
    printf("Hello world!\n");
}
```

Add language identifier next to three `` ` `` or `~` to turn on syntax highlight. There is 'c' identifier next to  the first `~~~` in following code block. 

```c
int main{
    printf("Hello world!\n");
}
```


# Table

Use at least three `-` and one `|` to create a table.
Use `:` to align column texts.
Text emphasis, link, and code in line can be used in tables.

|Heading 1      |Heading 2      |Heading 3      |
|:--------------|:-----------:  |---:           |
|*text 1*       |**text 2**     |***text 3***   |
|`text 1234`    |text `4123`    |[markdown](https://markdown.com.cn/basic-syntax/images.html)|


# Escaping Characters

Use `\` to type escaping characters.

|Escaping Character |Display        |
|:---               |:---           |
|`\\`               |\\             |
|`` \` ``           |\`             |
|`\*`               |\*             |
|`\_`               |\_             |
|`\{, \}`           |\{, \}         |
|`\[, \]`           |\[, \]         |
|`\(, \)`           |\(, \)         |
|`\#`               |\#             |
|`\+`               |\+             |
|`\-`               |\-             |
|`\.`               |\.             |
|`\!`               |\!             |
|`\|`               |\|             |


# Emoji

Use `:<emoji_code>:` to add emojis. 

:smiley: :blush: :joy:

For list of all available emojis, check [emoji list](https://github.com/ikatyang/emoji-cheat-sheet).
