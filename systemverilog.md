# Introduction

SystemVerilog is a hardware description and verification language 
used in the design and verification of digital systems.
It extends the capabilities of Verilog and inculdes features for design, testbench development, and verification.

In digital circuit developmet flows, 
SystemVerilog is mainly used in **verifications**, 
while designs are implemented almost by Verilog. 


# SystemVerilog Data

A data type is a **set** of values and a set of operations that can be performed on those values.
A data object is a named **entity** that has a data value and data type associated with it. 
Data types cn be used to declare data object or to define user-defined data types. 

SystemVerilog value set consists of four basic values: 
- `0`, a logic zero or a false condition
- `1`, a logic one or a true condition
- `x`, an unkown logic value
- `z`, a high-impedance state

Data types are categorized as either singular or aggregate. 
A singular variable or expression represents a single value, symbol, or handle. 
An aggregate varibale or expression represents a set or collection of singular values. 
Unpacked structure, unpacked union, or unpacked array are of aggregated vraibles. 
Others are of singular variables. 


## Basic data types

New data types in SystemVerilog compared to Verilog are introduced. 


### logic

`logic` data type is a 4-state type. 
The default value of `logic` variables is `x`. 

`logic` can replace `wire` and `reg` data types in Verilog for **both sequential and combinational logic**, 
meanwhile with **continuous assignments and procedural assignments**. 
However, `logic` can be driven by only 1 source.

`integer i0` is as the same as `bit signed [31: 0] i0;`.


### 2-state variables

|Data Type  |Bit Width  |Default Range  |Description                        |
|:---       |:---       |:---           |:---                               |
|`bit`      |1          |unsigned       |could be used to make up vectors   |
|`int`      |32         |signed         |                                   |
|`byte`     |8          |signed         |                                   |
|`shortint` |16         |signed         |                                   |
|`longint`  |64         |signed         |                                   |

`byte b0;` is as the same as `bit signed [ 7: 0] b0;`.


### String

`string` is a singular data type.
`string` data type is an ordered collection of characters. 
The length of a `string` variable is the number of characters in the collection. 
`string` variables are dynamic as their length may vary during simulation. 
A single character in a `string` variable could be selected. 
A single character in a `string` variable is of `byte`. 

Available methods: 
- `len()`
- `compare()`
- `toupper()`
- `tolower()`
- ...


### Enumeration

An enumeration type declares a set of integral named constants, 
which can be declared as following: 

```
enum [<enum_type>] {<enum_name_declaration> [, <enum_name_declaration>]} <enum_var_name>;
```

The default `<enum_type>` is `int`.
Both the enumeration names and their values should be unique. 
The default value of the first name is 0. 
The values can be set for some of the names and not set for other names. 
A name without a value is automatically assigned an increment of the value of the previous name.

`<enum_name_dclaration>[N]` could be used to generate N named constants: 
enum\_name\_dclaration0, enum\_name\_dclaration1, ...

Available built-in methods: 
- `num()`
- `name()`
- `first()`
- `last()`
- `next(<N>)`
- `prev(<N>)`



## Data structure

### Arrays

There are packed arrays and unpacked arrays in SystemVerilog. 
Packed array is used to refer to arrays with dimension declaration before the data identifier.
Unpacked array is used to refer to arrays with dimension declaration after the data identifier.

```
bit     [ 7: 0]         b1;             //  packed array, a vector
bit     [ 3: 0] [ 7: 0] b2;             //  packed array, multidimensional
real                    r1  [ 7: 0];    //  unpacked array
logic   [ 7: 0]         l1  [ 3: 0];    //  unpacked array
```

A packed array is guaranteed to be represented as a contiguous set of bits, 
an unpacked array may or may not be so represented. 

A one-dimenional packed array is often referred to as a vector. 
Multidimensional packed arrays are also allowed. 

Unpacked arrays may be fixed-size array, dynamic array, associative array, or queues.

If a packed array is declared as signed, 
the array viewed as a single vector is signed. 
The individual elements of the array are unsigned unless they are of a named type declared as signed. 
If an unpacked array is declared as signed, 
this applies to all individual elements of the array. 


#### Fixed-size array

A fixed-size array shall be represented by an address range.
The following declarations are equivalent. 

```systemverilog
int     arr [ 0: 7] [0:15];
int     arr [8]     [32];
```


#### Dynamic array

The size of a dynamic array can be set or changed at run time. 
The default size of an uninitialized dynamci array is zero. 
Any unpacked dimension in an array declaration may be a dynamic array dimension.
A delcaration example: 
```systemverilog
bit     [15: 0] b0 [];
```

The **`new []`** constructor is used to set or change the size of the dynamic array. 
It may appear in place of the right-hand side expression of variable declaration assignments 
and blocking procedural assignments when the left-hand side indicates a dynamic array. 

```systemverilog
int     arr1[], arr2[2][][], src[3], dest1[], dest2[];

arr             = new[4];           //  initialized with default int values
arr2[0]         = new[4];           //  dynamic subarray arr[0] sized to length 4
arr2[0][]       = new[2];           //  dynamic subarray arr[0][0] sized to length 2
arr2[1][0]      = new[2];           //  illegal, arr2[1] not initialized
arr2[0][]       = new[2];           //  illegal, syntax error
arr2[0][1][1]   = new[2];           //  illegal, arr2[0][1][1] is an int element

src             = '{2, 3, 4};       //  the ' is necessary
dest1           = new[2] (arr);     //  dest1 is {2, 3}
dest2           = new[4] (arr);     //  dest2 is {2, 3, 4, 0}, appended with default int value
dest2           = new[8] (dest2);   //  doubled dest2 size and remained values.
```

Available built-in methods: 
- `size()`, returns the size of the dynamic array. 
- `delete()`, clears all elements of the dynamic array and yield an empty array. 


#### Associative array

Associative array is a good option for the data collection with unknown size or sparse data space.  

An associative array implements a lookup table of the elements of its declared type. 
The declaration should be like: 
```
<data_type> <array_name> [<index_type>];
```

Wildcard index type like `<data_type> <array_nme> [*]` may be indexed by any integral expression 

Available built-in methods: 
- `num()` and `size()`
- `delete([<index>])`
- `exists(<index>)`, checks whether an element exists at the specifed `<index>`. 
- `first(<variable_name>)`, assigns to the `<variable_name>` the value of the first (smallest) index in the associative array 
- `last(<variable_name>)`, assigns to the `<variable_name>` the value of the last (largest) index in the associative array
- `next(<index>)`, returns the smallest index whose value is greater than th given `<index>` 
- `prev(<index>)`, returns the largest index whose value is smaller than th given `<index>` 



#### Queue

A queue is a dynamic ordered collection of homogeneous elements. 
A queue supports constatnt-time access to all its elements. 
Each elements in a queue is identified by a ordinal number that represents its position within the queue, 
with `0` representing the first, and `$` representing the last. 
Queues can be manipulated using the indexing, concatenation, slicing operator syntax, and equality operators. 

```systemverilog
byte        q1  [$];                //  a queue of bytes
integer     q2  [$] == {2, 3, 9}    //  an initialized queue of integers
bit         q3  [$:255];            //  a queue of bit with maximum size of 256
```

Available built-in methods: 
- `size()`, returns the size of the dynamic array. 
- `insert(<queue_index>, <element>)`, 
insert `<element>` before the `<queue_index>` element
- `delete([<queue_index>])`, delete the `<queue_index>` element.
If `<queue_index>` is not specified, the whole queue will be deleted. 
- `push_front(<element>)`
- `pop_front()`
- `push_back(<element>)`
- `pop_back()`


#### Array assignment

Array assignments rules: 
- The element types of source and target shall be equivalent.
- If the target is a fixed-size array, 
the size of both assignment side should be equicalent.


#### Multidimensional arrays

A multidimensional array is an array of arrays. 
A multidimensional array delcaration example: 

```systemverilog
bit     [ 3: 0] [ 7: 0]     b0  [ 0: 9];
```

The dimensions preceding the identifier set the packed dimensions (`[ 3: 0] [ 7: 0]`).
The dimensions following the identifier set the unpacked dimension (`[ 0: 9]`).
When referenced, the packed dimensions follow the unpacked dimensions. 
The rightmost dimension varies most rapidly and is the first to be omitted. 


#### Array manipulation methods

Systemverilog provides several built-in methods for arrays. 
```
<array_name>.<array_method>[(<iterator_argumemt>)] [with (<expression>)]
```

The `with` clause filter or pre-process elements according to `<expression>`. 


##### Array locator methods

Array locator methods operate on any unpacked array and return a queue. 
Array locator methods traverse the array in an unspecified order. 

`with` clause is mandatory as a filter in following methods: 
- `find() with(<expression>)`
- `find_index() with(<expression>)`
- `find_first() with(<expression>)`
- `find_first_index() with(<expression>)`
- `find_last() with(<expression>)`
- `find_last_index() with(<expression>)`

`with` clause is optional in following methods: 
- `min()`
- `max()`
- `unique()`
- `unique_index()`


##### Array ordering methods

Array ordering methods reorder elements of arrays except for associative array. 

Array ordering methods consist of: 
- `reverse()`
- `sort()`
- `rsort()`
- `shuffle()`


##### Array reduction methods

Array reduction methods are used to reduce the array to a single value. 
The `with` clause is used to pre-process elements before reduction operations. 

Array reduction methods consist of: 
- `sum()`
- `product()`
- `and()`
- `or()`
- `xor()`


##### Iterator index querying

`index(<dimension>)` returns the index of elements in arrays 
during array manipulation iterations.


#### Foreach-loop

`foreach` loop is useful in arrays processing. 

```systemverilog
foreach (arr[i, j]) begin
    $display(arr[i][j]);
end
```


### Structure

A `struct` represents a collection of data types that can be referenced as a whole, 
or the individual data types that make up the structure can be referenced by name.
By default, structures are unpacked, 
meaning that there is an implementation-dependent packing of the data types. 
Unpacked structures can contain any data type.

```
struct [packed [signed | unsigned]] {<struct_content>} <struct_name>;
```

A packed structure consisits of bit fields, 
which are packed together in memory without gaps.
An unpacked structure has an implementation-dependent packing, 
normally matching C compiler.
When a packed structure appears as a primary, 
it should be treated as a single vector available with arithmetic and logical operators.

If any data type within a packed structure is 4-state, 
the structure as a whole is treated as a 4-state vector. 
If there are also 2-state members in the structure, 
there is an implicit conversion from 4-state to 2-state 
when reading those members and from 2-state to 4-state when writing them.

Members in a `struct` could be referenced by `<struct_name>.<member_name>`. 


### Union

A `union` is a data type that represents a single piece of storage 
that can be accessed using one of the named member data types. 
Only one of the data types in the union can be used at a time. 
By default, a union is unpacked, 
meaning that there is an implementation-dependent packing of the data types. 

```
union [packed [signed | unsigned]] {<struct_content>} <struct_name>;
```

Packed unions shall only contain members that are of integral data types. 
The members of a packed, untagged union shall all be the same size. 
Thus, a union member that was written as another member can be read back. 
A packed union differs from an unpacked union in that when a packed union appears as a primary, 
it shall be treated as a single vector available with arithmetic and logical operators.

Only packed data types and the integer data types are legal in packed unions.


## User defined data type

`typedef` could be used to define complex data types with 
`struct`, `union`, `class`, `enum`, or basic data types. 

```
typedef <type_definition> <type_name>;
```


