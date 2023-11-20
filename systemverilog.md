# Introduction

SystemVerilog is a hardware description and verification language 
used in the design and verification of digital systems.
It extends the capabilities of Verilog and inculdes features for design, testbench development, and verification.

In digital circuit developmet flows, 
SystemVerilog is mainly used in **verifications**, 
while designs are implemented almost by Verilog. 


# Design Element

- module
- program
- interface
- checker
- package
- primitive
- configuration


# Scheduling Semantics

SystemVerilog and Verlog are both parallel programming languages. 
The execution of certain language constructs is defined by parallel execution of blocks or processes. 
It is important to understand what execution order is guaranteed to the user and what execution order is indeterminate.

Terms in an event execution model: 

- *Process*, concurrently scheduled elements, 
like modules, initial and always procedures, continuous assignments, procedural assignments, asynchronous tasks...
- *Updata evnet*: change in state of a net or variable. 
- *Evaluation event*: evaluation of a process.
- *Simulation time* 


## Verilog stratified event queue

Verilog event queue consisits of 5 regions: 

1. ***Active events***, 
occur at the current simulation time and can be processed in any order (causes nondeterminism). 
Processing of all the active events is called a *simulation cycle*. 

2. ***Inactive events***, 
occur at the current simulation time, 
but shall be processed after all the active events, 
like an explicit zero delay (`#0`). 

3. ***Noblocking assign update events***, 
events have been evaluated in previous simulation time, 
but shall be assigned at this simulation time. 

4. ***Monitor events***, 
like `$monitor` and `$strobe` system tasks. 

5. ***Future events***, 
are divided into *future inactive events* and *future nonblocking assignment update events*. 

The callback procedures scheduled with PLI routines shall be treated as inactive evnets. 

Events can be added to any of the regions, 
but are only removed from the *active region*. 
Active events are updeted or evaluated firstly, 
and the events are activated by the order of inactive events, 
nonblocking assign update events, monitor events, 
and then advance to next event time and active future events.

\<diagram\>


## SystemVerilog stratified event scheduler

Every event has one and only one simulation execution time. 
All scheduled events at a specific time define a time slot.


The simulation regions of a time slot consist of: 

1. ***Preponed Events Region***, 
sampling in the preponed region is identical to sampling in the previous postponed region.

2. ***Active Events Region***, 
holds current active events being evaluated. 

3. ***Inactive Events Region***, 
holds events to be evaluated after active events, 
like an explicit zero delay `#0`. 

4. ***NBA***
i.e. Nonblocking Assignment Update Events Region, 
holds events to be evaluated after inactive evnets, 
like a nonblocking assignment. 

5. ***Observed Events Region***, 
is for evaluation of property expressions. 

6. ***Reactive Events Region***, 
the code specified by blocking assignments in checkers, program blocks 
and the code in action blocks of concurrent assertions are scheduled in the Reactive region.

7. ***Re-Inactive Events Region***
holds events to be evaluated after reactive events, 
like an explicit zero delay `#0`. 

8. ***Re-NBA Events Region***
holds events to be evaluated after re-inactive evnets, 
like a nonblocking assignment. 

9. ***Postponed Events Region***
holds `$monitor`, `$strobe`, and other events. 

In addition to simulation regions, 
the PLI (Programming Language Interface) regions of a time slot consist of: 

1. ***Pre-Active***

2. ***Pre-NBA***

3. ***Post-NBA***

4. ***Pre-Observed***

5. ***Post-Observed***

6. ***Pre-Re-NBA***

7. ***Post-Re-NBA***

8. ***Pre-Postponed***

\<diagram\>


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


## Singular data types

New data types in SystemVerilog compared to Verilog are introduced. 


### Logic

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


## Aggragate data types

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


## Casting

A data type can be changed by using `'` operation: 
```
<target_type>'(<expression>)
```


## Const constants

A `const` form of constant differs from a `localparam` constant in that 
the `localparam` shall be set during elaboration, 
whereas a `const` constant can be set during runtime. 

```
const <data_type> <var_name> = <value>
```


# Class


# Processes

# Structured procedure

Structured procedures includes: 
- initial
- always
- final
- task
- function


### Fuction and task

The `begin` and `end` identifiers are optional in task or function definitions. 

`return` can be used to terminate a fucntion or task.

`void` can be used in function delcaration to ignore return value. 

`ref` can be used to pass a reference of a variable to a function or task, 
which is useful to pass array arguments without duplication. 

Defualt values of arguments can be set in a function or task. 

A taks or a fucntion can be delcared as `automatic`. 
Automatic tasks and functions can be invoked recursively. 


## Block statement

### Parallel blocks

A `fork-join` parallel block in a procedure 
creates concurrent processes from each of its statements.

```
fork [: block_name]
    [item_delcarations]
    [statements]
join | join_any | join_none
```

- `join`, 
    the parent process stops 
    until all the processes spawned by this fork complete
- `join_any`, 
    the parent process stops 
    until any one of the processes spawned by this fork completes.
- `join_none`, 
    the parent process continues to execute 
    concurrently with all the processes spawned by the fork. 
    The spawned processes do not start executing 
    until the parent thread esecutes a blocking statement or terminates.


## Procedural programming statements

Including: 
- Consitional if-else statement
- Case statement
- Pattern matching conditional statements
- Loop statements
- Jump statements

### Loop statements

New loop statements contrast to verilog: 
- `foreach (<array>) begin ... end`
- `do ... while (<condition>)`

`++` and `--` are available in systemverilog and are helpful in loop statements. 

In `for` loop statements, local variable delcaration is legal in initialization statement.


### Jumpstatements

- `continue`
- `break`
- `return`


# Operators

New operators compared to verilog: 
- `+=`, `-=`, `*=`, ...
- `++`, `--`
- streaming operators


## Streaming operator

Streaming operators perform packing of bit-stream types into 
a sequence of bits in a user-specified order. 
When used in the left-hand side, 
the streaming operators upack a stream of bits into one or more vairables. 

```
{<stream_operator> [<slice_size>] {<value>[ , <value>]}}
```

where `<stream_operator>` are `>>` which means which means original order, 
or `<<` which means inverted order.


# Clocking Block

A clocking block is defined between the keywords `clocking` and `endclocking`.
Clocking block construct identifies clock signals and 
captures the timing and synchronization requirements of the blocks being modeled. 
A clocking block assembles signals that are synchronous to a particular clock and 
makes their timing explicit.


## Clocking block declaration

```
clocking <clocking_name> <clocking_event> ;
    <clocking_signal_direction> [<clocking_skew>] <clocking_signal_name>;
endclocking
```

The `<clocking_skew>` determines how many time units away from 
the clock event a signal is to be sampled or driven.

*Example:*
```systemverilog
clocking bus @(posedge clock1);
    default input #10ns output #2ns;
    input data, ready, enable = top.mem1.enable;
    output negedge ack;     //  driven on the negative edge of the clock
    input #1step addr;
endclocking
```

In the preceding example, the last two delcarations overrides the default skew. 


## Input and output skews

Input (or inout) signals are sampled at the designated clock event. 
If an input skew is specified, then the signal is sampled at skew time units before the clock event. 
Similarly, output (or inout) signals are driven skew simulation time units after the corresponding clock event. 

## Cycle delay

`## <N>` could be used to delay for N clocking events. 


# Static and Automatic 

`automatic` can be used in varaible, task, function, 
module, interface, program, and pakcage delcarations. 
By defualt, delcarations are static. 

An automatic delcaration will create specific variable storage for each invocation. 
A static or default declaration will share a common variable storage on each invocation. 


# Assertions


# Constrained Random Value Generation


# Program

The program construct serves as a clear separator between design and testbench, 
and, more importantly, it specifies specialized execution semantics in the reactive region set 
for all elements declared within the program. 
Together with clocking blocks, 
the program construct provides for race-free interaction between the design 
and the testbench and enables cycle- and transaction-level abstractions.


# Interface

The interface construct, enclosed between the keywords `interface...endinterface`, 
encapsulates the communication between design blocks, and between design and verification blocks. 
At its lowest level, an interface is a named bundle of nets or variables. 
Modules that are connected via an interface can simply call the subroutine menbers of that 
interface to drive the communication. 
Interface can aslos contain processes and continuous assignments, 
which makes protocol checking, coverage recording, reporting, and assertions possible in interfaces. 


## Interface declaration 

```
interface <interface_name> [(<interface_ports>)]
    [<clocking_block_declarations>]
    [<interface_parameters>]
    <port_declarations>
    [<modport_declarations>]
    [<process_declarations>]
endinterface
```

An interface can be instantiated like a module. 

The difference between nets or variables in the interface port list and 
other nets or variables within the interface is that 
only those in the port list can be connected externally 
by name or position when the interface is instantiated.


## Modport

`modport` is used to indicate the directions during port declarations within interface. 
As the name indicates, the directions are those **seen from the module**. 

```
modport <modport_name> (<direction> <port_name>[, <direction> <port_name>])
```

A modport expression allows elements declared in an interface to be included in a modport list. 
For example: 

```systemverilog
interface I;
    logic [7:0] r;
    const int x=1;
    bit R;
    modport A (output .P(r[3:0]), input .Q(x), R);
    modport B (output .P(r[7:4]), input .Q(2), R);
endinterface

module M ( interface i);
    initial i.P = i.Q;
endmodule

module top;
    I i1 ();
    M u1 (i1.A);
    M u2 (i1.B);
    initial #1 $display("%b", i1.r); // displays 00100001
endmodule
```

The modport construct can also be used to specify 
the direction of clocking blocks declared within an interface.
All of the clocking blocks used in a modport declaration shall be declared 
by the same interface as the modport itself.
Like all modport declarations, 
the direction of the clocking signals are those seen 
from the module in which the interface becomes a port.

