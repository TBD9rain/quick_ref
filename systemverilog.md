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
the PLI (Programming Language Interface) regions of a time slot, 
which provide a PLI callback control point 
that allows PLI application routines to read values, write values or create events. 

1. ***Pre-Active***,
2. ***Pre-NBA***
3. ***Post-NBA***
4. ***Pre-Observed***
5. ***Post-Observed***
6. ***Pre-Re-NBA***
7. ***Post-Re-NBA***
8. ***Pre-Postponed***

\<diagram\>


## Determinism and Nondeterminism

Determinism: 
- Statements within a begin-end block shall be executed in the order in which they appear in that begin-end block. 
- Nonblocking assignments (NBAs) shall be performed in the order the statements were executed. 

Nondeterminism
- Active events can be taken off the Active or Reactive event region and processed in any order.
- Statements without time-control constructs in procedural blocks do not have to be executed as one event.


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

Class handles are singular. 
But classes need not be categorized as singular or aggregate. 


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
which can be declared as follows: 

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


### Event

`event` provides a powerful and efficient handle to a synchronization object. 
The object referenced by an event variable can be explicitly triggerd and waited for. 

```systemverilog
event done              ;      // declare a new event called done
event done_too = done   ;      // declare done_too as alias to done
event empty = null      ;      // event variable with no synchronization object
```

To trigger an event, use `->` operator or `->>`: 
```systemverilog
->  done    ;   //  usual trigger
->> done    ;   //  trigger the referenced event in the nonblocking assignment region
```

To wait an event, use `@` operator: 
```systemverilog
@ done_too;
```

`wait_order` construct could be used to suspends the calling process 
until all of the specified events are triggered in the given order (left to right) 
or any of the untriggered events are triggered out of order and thus causes the operation to fail.
```
wait_order (<ordered_event_list>) [<statements>]
[else [<statements>]]
```


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

Class is a data type which consists of properties (data) and methods (fucntions and tasks). 
Objects instatiating classes could be created and destroyed dynamically. 

```
class <class_name> [#(<parameter_and_type_list>)]
    [extends <base_class_name> [#(<parameter_and_type_list>)]]                          //  inheritance
    ;
    [static ][local | protected ][random | randomc ][const ]    <class_properties_declarations>
    [extern ][static ][virtal ][local | protected ]             <class_subroutines_declarations>
endcalss
```

For example: 
```systemverilog
class Packet;
    int a = 0;
    static int b = 1;
endclass
```


## Object

An object is used by first declaring a variable (handle) of that class type 
and then creating an object of that class (using the `new` function) 
and assigning it to the variable.

For example:
```systemverilog
Packet p;
p = new;
```

`==`, `!=` with another calss object or with null is valid. 
Object data and methods could be accessed with a class scope resolution operator: 
```systemverilog
$display(p.a);
```

Methods shall be declared as automatic. 
Using `static` qualifier with method declaration is illegal. 
However, there are staitc methods. 

Class parameters and types can be changed during object declaration like parameters in a module.
Class parameters could be accessed by object like a property or by class like a static property.  
Class type could only be accessed by class like a statice  property

## Constructors

If a class does not provide an explicit user-defined `new` method, 
an implicit new method shall be provided automatically.
An explicit user-defined `new` method could be declared as: 

```
class Packet;
    int a = 0;

    function new(a);
        this.a = a;
    endfunction
endclass
```

`this` is similar to `self` in python. 
The `this` keyword shall only be used within non-static class methods, 
constraints, inlined constraint methods, or covergroups embedded within classes;

The `new` method of a derived class shall first call its base class constructor `super.new()` 
in the **first line of its `new` method**.
After the properties are initialized, 
the remaining code in a user-defined constructor shall be evaluated.

`super.<super_member>` could be used to invoke data or mehtods of base class. 


## Class copying

Considering `Packet` is a class and: 

```systemverilog
Packet  p0;
Packet  p1;
Packet  p2;

p0  = new;
p1  = p0;
p2  = new p0;
```

After preceding codes, a new `Packet` object was created and referred by `p0`, 
`p1` refer to the same object as `p0`, 
`p2` refer to another object with same values as `p0` (`p1`). 

In `p2`, all variables of `p0` (`p1`) are copied: integers, strings, instance handles, etc. 
Objects, however, are not copied, only their handles in `p0` (`p1`); 
as before, two names for the same object have been created. 
To do a full (deep) copy, where everything (including nested objects) is copied, 
customized copy method is typically needed.


## Static property

Properties in class declarations are automatic by default. 
To access a static class property, use`<clasee_name>::<property>`. 
Static properties are independnet to of objects, 
which could be used without creating an object. 


## Static methods

Static methods behave like regular subroutines, 
which can access static class properties or call static methods of the same class.
Access to non-static members or to the special `this` handle 
within the body of a static method is illegal and results in a compiler error.

```systemverilog
class TwoTasks;
    static task t1(); ... endtask       // static class method with
                                        // automatic variable lifetime

    task static t2(); ... endtask       // ILLEGAL: non-static class method with
                                        // static variable lifetime
endclass
```


## Protection

Class properties and methods are public by default. 
Class parameters and class local parameters are also public.

Class properties and methods could be qualified by: 

- `local`, 
only available to methods inside the class. 
Local members are not visible within subclasses. 

- `protected`, 
identical to `local`, 
except that protected members is visible to subclasses.

A class method could be qualified with `virtual` as well. 
A virtual method shall override a method in all of its base classes, 
whereas a non-virtual method shall only override a method in that class and its descendants.


## Method declarations out of class

The `extern` qualifier indicates that 
the body of the method (its implementation) is to be found outside the declaration.


## Virtual methods

A virtual method shall override a method in all of its base classes, 
whereas a non-virtual method shall only override a method in that class and its descendants.

```systemverilog
class BasePacket;
    int A = 1;
    int B = 2;

    function void printA;
        $display("BasePacket::A is %d", A);
    endfunction : printA

    virtual function void printB;
        $display("BasePacket::B is %d", B);
    endfunction : printB
endclass : BasePacket

class My_Packet extends BasePacket;
    int A = 3;
    int B = 4;

    function void printA;
        $display("My_Packet::A is %d", A);
    endfunction: printA

    virtual function void printB;
        $display("My_Packet::B is %d", B);
    endfunction : printB
endclass : My_Packet

BasePacket P1 = new;
My_Packet P2 = new;

initial begin
    P1.printA;      // displays 'BasePacket::A is 1'
    P1.printB;      // displays 'BasePacket::B is 2'
    P1 = P2;        // P1 has a handle to a My_packet object
    P1.printA;      // displays 'BasePacket::A is 1'
    P1.printB;      // displays 'My_Packet::B is 4' – overidden by subclass
    P2.printA;      // displays 'My_Packet::A is 3'
    P2.printB;      // displays 'My_Packet::B is 4'
end
```


## Abstract classes and pure virtual methods

Abstract classes are frameworks for its subclasses. 
Abstract classes are qualified with `virtual`: 

```
virtual class <abstract_class>
    pure virtual function <function_name> [<port_list>];
endclass
```

An object of an abstract class shall not be constructed directly. 
Its constructor may only be called indirectly through the chaining of constructor calls from an extended non-abstract object.

A pure virtual method is declared as a prototype withou implementation, 
which is qualified with `pure virtual`. 
An extended subclass may provide an implementation within a virtual function with identical name. 


# Processes

## Structured procedure

Structured procedures includes: 
- initial
- always
- final
- task
- function

A `final` procedure executes when simulation ends 
due to an explicit or implicit call to `$finish`. 


### Fuction and task

The `begin` and `end` identifiers are optional in task or function definitions. 

`return` can be used to terminate a fucntion or task.

`void` can be used in function delcaration to ignore return value. 

`ref` can be used to pass a reference of a variable to a function or task, 
which is useful to pass array arguments without duplication. 

Defualt values of arguments can be set in a function or task. 

A taks or a fucntion can be delcared as `automatic`. 
Automatic tasks and functions can be invoked recursively. 

SystemVerilog allows arguments to tasks and functions to be bound by name as well as by position like module ports. 

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


### Jump statements

- `continue`
- `break`
- `return`


# Operators

New operators compared to verilog: 
- `+=`, `-=`, `*=`, ...
- `++`, `--`
- streaming operators
- set membership operator `inside`


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


## Set membership operator

The syntax for the set membership operator is as follows: 

```
<expression> inside {<set>}
```

The members of the `<set>` are scanned until a match is found and the operation returns `1'b1`.
The inside operator uses the equality operator (`==`) on nonintegral expressions to perform the comparison. 
If no match is found, the inside operator returns 1'b0.

`<set>` is a comma-separated list of expressions of ranges. 
A range can be specified as `[low_bound:high_bound]`. 
A bound specified by `$` shall represent the lowest or highest value. 
If an expression in the list is an unpacked array, 
its elements are traversed by descending into the array until reaching a singular value. 
Values can be repeated; therefore, values and value ranges can overlap. 


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
By defualt, delcarations are **static**. 

An automatic delcaration will create specific variable storage for each invocation. 
A static or default declaration will share a common variable storage on each invocation. 


# Assertions

Assertions are used to validate the behavior of a design and provide functional coverage. 

Assertion statements consist of: 

- `assert`
- `assume`
- `cover`
- `restrict`

Assertions are divided into concerrent and immediate assertions. 
Immediate assertions are executed like a statement in a procedural block. 
Immediate assertions are primarily intended to be used with simulation. 
There is no immediate restrict assertion statement.
Concurrent assertions are based on clock semantics and use sampled values of their expressions. 
Concurrent assertions are evaluated in the Observed region.


## Imediate assertions

In a simple immediate assertion, 
pass and fail statements take place immediately upon assertion evaluation.
```
[<assertion_name>:] {assert | assume | cover} (expression) 
    [<pass_statements>]
[else]
    [<fail_statements>]
```

In immediate `assert` statement, its expression is required to be true. 
If no `else` clause is specified, 
failure of an immediate assert statement will call `$error` by default. 
Immediate `assume` may behave as immediate `assert`. 

System tasks like `$error`: 
- `$fatal`
- `warning`
- `$info`

`<assertion_name>:` provides name displaying by hierarchical name of the scope. 


In a deferred immediate assertion, 
the statements are delayed until later in the time step. 
```
{assert | assume | cover} {# 0 | final}(expression) 
    [<pass_statements>]
[else]
    [<fail_statements>]
```

Differences between defered immediate assertions and simple immediate assertions: 
- Reporting is delayed rather than being reported immediately.
- Statements may only contain a single subroutine call.
- A deferred assertion may be used as a module common item.



# Constrained Random Value Generation

The random constraints are typically specified on top of an object-oriented data abstraction 
that models the data to be randomized as objects 
that contain random variables and user-defined constraints.

## Random variables

Class properties can be declared random using the `rand` and `randc` qualifiers. 
The syntax of random variables within class declarations is as follows: 

```systemverilog
class <class_name>
    rand    [<other_qualifier> ]   <property_declarations>
    randc   [<other_qualifier> ]   <property_declarations>
endclass
```

Variables declared with the `rand` keyword are standard random variables. 
Their values are **uniformly distributed** over their range.

Variables declared with the `randc` keyword are random-cyclic variables 
that cycle through all the values in a random permutation of their declared range.
With `randc`, all possible values satisfying constraints are iterated in a random order. 


### Sigular vairbales

All singular variables of any intgral type can be randomized using `rand` or `randc`. 

For each active random variable of `enum` type, 
the solver shall select a value from the set of named constants defined by the corresponding `enum`.


### Fixed-size arrays

Fixed-size arrays can be declared as `rand` or `randc`, 
in which case all of their member elements are treated as rand or randc.
Individual array elements can be constrained, 
in which case the index expression may include iterative constraint loop variables, constants, and state variables.


### Dynamic arrays

Dynamic arrays can be declared as `rand` or `randc`. 
All of the elements in the array are randomized, overwriting and previous data. 

The size of a dynamic array declared as `rand` or `randc` can be constrained. 
If a dynamic array's size is not constrained, then the array shall not be resized. 
When a dynamic array is resized by `randomize()`, 
the resized array is initialized with the original array. 
Any new elements inserted take on the default value of the element type.

If the elements in the dynamic array are class objects, 
randomize() does not allocate any class objects. 
Up to the new size, existing class objects are retained and their content randomized. 
If the new size is greater than the original size, 
each of the additional elements has a null value requiring no randomization.

In resizing a dynamic array by `randomize()` or new, 
the `rand_mode` of each retained element is preserved 
and the `rand_mode` of each new element is set to active.


### Associative arrays

Associative arays can be declared as `rand` or `randc`. 
All of the elements in the array are randomized, overwriting and previous data. 


### Queues

Queues can be declared as `rand` or `randc`. 
All of the elements in the array are randomized, overwriting and previous data. 

The size of a queue declared as `rand` or `randc` can be constrained. 
When a queue is resized by randomize(), 
elements are inserted or deleted at the back of the queue as necessary to produce the new queue size.
Any new elements inserted take on the default value of the element type.

If the elements in the queue are class objects, 
randomize() does not allocate any class objects. 
Up to the new size, existing class objects are retained and their content randomized. 
If the new size is greater than the original size, 
each of the additional elements has a null value requiring no randomization.

In resizing a queue by `randomize()` or new, 
the `rand_mode` of each retained element is preserved 
and the `rand_mode` of each new element is set to active.


### Structure

An unpacked structure can be declared as `rand` but not `randc`, 
in which case all of that structure’s random members are solved concurrently. 
A structure member can be declared as `rand` or `randc`. 

A packed structure can be declared as `rand` or `randc`, 
in which case that structure is treated as an integral type. 
Members of packed structures shall not have a random modifier. 


### Unions

A packed untagged union can be declared as `rand` or `randc`, 
in which case that union is treated as an integral type. 
Members of packed untagged unions shall not have a random qualifier.


### Class handles

Class handles can be declared as `rand` but not `randc`, 
in which case all of that object’s variables and constraints are solved concurrently 
with the variables and constraints of the object that contains the handle.


## Random Constraints

The values of random variables are determined using constraint expressions 
that are declared within constraint blocks. 
Constraint blocks are class members. 
Constraint block names shall be unique within a class.
The syntax of random constraints within class declarations is as follows:

```
class <class_name>
    <random_propery_delcarations>

    [static ]constraint <constraint_name> {<constraint_contents>}

    [extern | pure][static ] constraint <external_constraint_name> ;

endclass
```

Constraints follow the same general rules for inheritance as other class members. 


### External constraint blocks

An external constraint block shall appear in the same scope as the corresponding class declaration 
and shall appear after the class declaration in that scope. 
If the explicit form of constraint prototype is used, 
it shall be an error if no corresponding external constraint block is provided. 
If the implicit form of prototype is used and there is no corresponding external constraint block, 
the constraint shall be treated as an empty constraint and a warning may be issued. 
An empty constraint is one that has no effect on randomization, 
equivalent to a constraint block containing the constant expression 1.
For example:

```systemverilog
class C;
    rand int x;
    constraint proto1; // implicit form
    extern constraint proto2; // explicit form
endclass

constraint C::proto1 { x inside {-4, 5, 7}; }
constraint C::proto2 { x >= 0; }
```

An abstract class may contain pure constraints. 
A pure constraint is syntactically similar to an external constraint but uses the `pure` keyword. 


### Set membership

Constraints support the set membership operator `inside`. 
the nagated form of the `inside` operator denotes that expression lies outside the set. 
For example: 

```systemverilog
rand integer x, y, z;
constraint c1 {x inside {3, 5, [9:15], [24:32], [y:2*y], z};}

rand integer a, b, c;
constraint c2 {!(a inside {b, c});}

integer fives[4] = '{ 5, 10, 15, 20 };
rand integer v;
constraint c3 { v inside {fives}; }
```


### Distribution

In addition to set membership, 
constraints support sets of weighted values called distributions.
Without distributions, the probabilities of all valid values are equal. 

Distribution syntax: 

```
<expression> dixt {:= [| :/] <expression>}
```

A `dist` operation shall not be applied to `randc` variables.

The `:=` operator assigns the specified weight to the item or, 
if the item is a range, to every value in the range. 

The `:/` operator assigns the specified weight to the item or, 
if the item is a range, to the range **as a whole**. 
If there are n values in the range, the weight of each value is `range_weight / n`.

```
x dist { [100:102] := 1, 200 := 2, 300 := 5}    //  100, 101, 102, 200, or 300 with 
                                                //  a weighted ratio of 1-1-1-2-5
x dist { [100:102] :/ 1, 200 := 2, 300 := 5}    //  100, 101, 102, 200, or 300 with 
                                                //  a weighted ratio of 1/3-1/3-1/3-2-5.
```


### Unique constraints

`unique` qualifier could be used so that 
no two members of the group have the same value after randomization.
All members of the group of variables so specified shall be of **equivalent type**.
`unique` could not be used with `randc` variables. 

```systemverilog
rand byte a[5];
rand byte b;
rand byte excluded;
constraint u { unique {b, a[2:3], excluded}; }
constraint exclusion { excluded == 5; }
```

In the preceding example, 
variables `a[2]`, `a[3]`, `b`, and `excluded` will all contain different values after randomization. 
Because of the constraint exclusion, none of the variables `a[2]`, `a[3]`, and `b` will contain the value 5.


### Implication and if-else constraints

The if–else style constraint declarations are equivalent to implications

```systemverilog
    if (mode == little)
    len < 10;
    else if (mode == big)
    len > 100;
```

which is equivalent to

```systemverilog
    mode == little -> len < 10 ;
    mode == big -> len > 100 ;
```

Implication and if-else constraints are bidirectional.
The value of `mode` constrains the value of `len`, 
and the value of `len` constrains the value of `mode`.


### Iterative constraints

- `foreach`
- Array reduction: `with`


### Random variable solving order

```systemverilog
solve <random_variable> before <random_variables>
```

The variable ordering can be used to force selected corner cases to occur more frequently than they would otherwise.
For example: 

```systemverilog
class B;
    rand bit s;
    rand bit [31:0] d;

    constraint c { s -> d == 0; }
endclass
```

Where the probability of `s == 1` is `1/(1+2^32)`.

```systemverilog
class B;
    rand bit s;
    rand bit [31:0] d;

    constraint c { s -> d == 0; }
    constraint order { solve s before d; }
endclass
```

Where the probability of `s == 1` is `1/2`.


### Static constraints

Static constraints are constraints declared with qualifier `static`. 
If a constraint block is declared as static, 
then calls to `constraint_mode()` shall affect all instances of the specified constraint in all objects.


### Functions in constraints

Fuctions could be used in constraint expressions. 
And functions in constaints imposes certain semantic restrictions, as follows: 
- functions cannot contain `output` or `ref` arguments (`const ref` is allowed).
- functions should be automatic and have no side effects. 
- functions cannot modify the constraints, for example, calling `rand_mode` or `constraint_mode` methods.
- functions shall be called before constraints are solved. 
- random variables used as function arguments have higher implicit variable ordering priorities. 
- circular dependencies created by the implicit variable ordering shall result in an error. 
- function calls in active constraints are executed an unspecified number of times (at least once) in an unspecified order. 


### Soft constraints

When there is no solution that satisfies all active constraints simultaneously, 
the soft constraints will be discard generally in the declaration order, 
and find a solution that satisfies the remaining constraints.


## Randomization methods

`randomize()` is a built-in virtual method for every class, 
which is invoked to random values and cannot be overridden. 
When `randomize()` is called with arguments, 
those arguments designate the complete set of random variables within that object; 
all other variables in the object are considered state variables.


`pre_randomize()` and `post_randomize()` are automatically invoked before and after `randomize()`. 

Users can override the `pre_randomize()` in any class to perform 
initialization and set preconditions before the object is randomized. 
If the class is a derived class and no user-defined implementation of `pre_randomize()` exists, 
then `pre_randomize()` will automatically invoke `super.pre_randomize()`.

Users can override the `post_randomize()` in any class to perform 
cleanup, print diagnostics, and check post-conditions after the object is randomized. 
If the class is a derived class and no user-defined implementation of `post_randomize()` exists, 
then `post_randomize()` will automatically invoke `super.post_randomize()`.

If these methods are overridden, 
they shall call their associated base class methods; 
otherwise, their pre- and post-randomization processing steps shall be skipped.

```systemverilog
class XYPair;
    rand integer x, y;
endclass

class MyXYPair extends XYPair
    function void pre_randomize();
        super.pre_randomize();
        $display("Before randomize x=%0d, y=%0d", x, y);
    endfunction
    
    function void post_randomize();
        super.post_randomize();
        $display("After randomize x=%0d, y=%0d", x, y);
    endfunction
endclass
```


## In-line constraints

By using the `randomize() with` construct, 
users can declare in-line constraints at the point where the `randomize()` method is called.
For example: 
```systemverilog
class SimpleSum;
    rand bit [7:0] x, y, z;
    constraint c {z == x + y;}
endclass

task InlineConstraintDemo(SimpleSum p);
    int success;
    success = p.randomize() with {x < y;};
endtask
```

`randomize() with` is used to introduce an additional constraint that `x < y`.


## Enable random constraints and variables

The `constraint_mod()`method can be used to control whether a constraint is active or inactive. 
With argument `0` is to diable the random constraint. 

The `rand_mode()` method can be used to control whether a random variable is active or inactive. 
With argument `0` is to diable the random variable. 


# Functional Coverage

Coverage is defined as the percentage of verification objectives that have been met. 
There are two types of coverage metrics: *code coverage* and *functional coverage*. 
The code coverage can be automatically extracted from the design code. 
The functional coverage are user-defined in order to tie the verification environment to the design intent. 

The functional coverage could be reached with SystemVerilog functional coverage constructs. 


## Coverage model

The `covergroup` construct encapsulates the specification of a coverage model. 
The `covergroup` construct is a user-defined type. 
The type definition is written once, 
and multiple instances of that type can be created in different contexts. 
Similar to a `class`, once defined, a `covergroup` instance can be created via the `new()` operator. 
A covergroup can be defined in a package, module, program, interface, checker, or class.
```
covergroup <covergroup_name> [<coverage_evnet>];
    <coverage_specifications> ;
    <coverage_options> ;
endgroup
```

If a `<clocking_event>` is specified, 
it defines the event at which coverage points are sampled. 
If a `<clocking_event>` is not specified, 
users must procedurally trigger the coverage sampling via the built-in `sample()` method. 
`sample()` method could be overridden. 

A `covergroup` could contain one or more `<coverage_spcifications>`. 
`<coverage_spcifications>` could be cover\_point or cover\_cross. 

```systemverilog
enum    { red, green, blue }    color;
bit     [3:0]                   pixel_adr, pixel_offset, pixel_hue;

covergroup g2 @(posedge clk);
    Hue:    coverpoint  pixel_hue;
    Offset: coverpoint  pixel_offset;

    AxC:    cross       color, pixel_adr;       // cross 2 variables (implicitly declared coverpoints)
    all:    cross       color, Hue, Offset;     // cross 1 variable and 2 coverpoints
endgroup
```

A `covergroup` can also specify one or more `<coverage_options>` to control 
and regulate how coverage data are structured and collected.
Coverage options can be specified for the `covergroup` as a whole or 
for specific items within the coverage group, 
that is, any of its coverage points or crosses.


## Using covergroup in classes

By embedding a coverage group within a class definition, 
the covergroup provides a simple way to cover a subset of the class properties.

```systemverilg
class xyz;
    bit [3:0] m_x;
    int m_y;
    bit m_z;

    covergroup cov1 @m_z; // embedded covergroup
        coverpoint m_x;
        coverpoint m_y;
    endgroup

    function new(); 
        cov1 = new; 
    endfunction
endclass
```

A `covergroup` declaration within a class is an embedded covergroup declaration. 
An embedded `covergroup` declaration declares an anonymous covergroup type and 
an instance variable of the anonymous type. 
The `<covergroup_name>` defines the name of the instance variable. 
In the preceding example, 
a variable cov1 (of the anonymous coverage group) is implicitly declared.

An embedded coverage group can be explicitly instantiated in the new method. 
If it is not, 
then the coverage group is not created and no data will be sampled.


## Coverage points

The coverpoint syntax is as following: 
```
[<coverpoint_label>: ]
coverpoint <coverpoint_expression>
[ iff (<iff_expression>)]
{<coverpoint_bin>[ <coverpoint_bin>]} OR ;
```

If the label is specified, then it designates the name of the coverage point.
This name can be used to add this coverage point to a cross coverage specification 
or to access the methods of the coverage point.

A coverage point can sample the values that correspond to a particular scheduling region 
by specifying a clocking block signal. 
Thus, a coverage point that denotes a clocking block signal will sample the values made available by the clocking block. 
If the clocking block specifies a skew of #1step, 
the coverage point will sample the signal values from the Preponed region. 
If the clocking block specifies a skew of #0, 
the coverage point will sample the signal values from the Observed region. 

Only constant expressions, global and instance constants , or non-ref arguments to the covergroup 
are allowed to be used as variables in a `<coverpoint_expression>`. 

The expression within the `iff` construct specifies an optional condition 
that disables coverage for that coverpoint. 
If the guard expression evaluates to false at a sampling point, 
the coverage point is ignored. 


### Coverage point bins

A **value** bin could be created as following: 
```
[wildcard ]
bins OR illegal_bins OR ignore_bins
<bin_name> = {<range_list>}
[ with (<with_expression>)]
[ iff (<iff_expression>)]
;
```

A wildcard bin definition causes all `X`, `Z`, or `?` to be treated as wildcards for `0` or `1`.

The `ignore_bins` is used to explicitly excluded from coverage. 
The `illegal_bins` is used to explicitly excluded from coverage. 
If an illegal value or transition occurs, a runtime error is issued.

A coverage point bin associates a name and a count with a set of values or a sequence of value transitions. 
If the bin designates a set of values, 
the count is incremented every time the coverage point matches one of the values in the set. 
If the bin designates a sequence of value transitions, 
the count is incremented every time the coverage point matches the entire sequence of value transitions. 

The bins for a coverage point can be automatically created by SystemVerilog 
or explicitly defined using the bins construct to name each bin. 
If the bins are not explicitly defined, 
they are automatically created by SystemVerilog. 
The number of automatically created bins can be controlled using the `auto_bin_max` coverage option.

```systemverilog
bit [9:0] v_a;

covergroup cg @(posedge clk);
    coverpoint v_a
    {
        bins a = { [0:63],65 };
        bins b[] = { [127:150],[148:191] }; // note overlapping values
        bins c[] = { 200,201,202 };
        bins d = { [1000:$] };
        bins others[] = default;
    }
endgroup
```

In the preceding example, 
the first bins construct associates bin `a` with the values of variable `v_a` between 0 and 63 and the value 65. 
The second bins construct creates a set of 65 bins b[127], b[128],...b[191].
Likewise, the third bins construct creates 3 bins: c[200], c[201], and c[202]. 
The fourth bins construct associates bin d with the values between 1000 and 1023 ($ represents the maximum value of `v_a`). 
Every value that does not match bins a, b[], c[], or d is added into its own distinct bin.

The `default` specification defines a bin that is associated with none of the defined value bins. 
However, the coverage calculation shall not take into account the coverage captured by the default bin.

The `with` clause specifies that only those values in the `<range_list>` 
that satisfy the given `<with_expression>` are included in the bin.

A transition bin could be created as following: 
```
[wildcard ]
bins OR illegal_bins OR ignore_bins
<bin_name> [[]] = (<trans_range_list> => <trans_range_list>)[, (<trans_range_list> => <trans_range_list>)]
[ iff (<iff_expression>)]
;
```

The `<trans_range_list>` is consists of values and optional repetition indicator. 

```systemverilog
1 => 2              //  1 to 2
1, 2 => 2, 3        //  1 to 2 or 1 to 3 or 2 to 2 or 2 to 3
3 [* 5]             //  3 => 3 => 3 => 3 => 3
3 [* 3:5]           //  3 => 3 => 3, 3 => 3 => 3 => 3, 3 => 3 => 3 => 3 => 3
... => 4            //  any value except 4 to 4
3 [-> 2] => 5       //  .. => 3 ... => 3 => 5
3 [= 2] => 5        //  .. => 3 ... => 3 ... => 5
```

A transition bins example: 
```systemverilog
bit [4:1] v_a;

covergroup cg @(posedge clk);
    coverpoint v_a
    {
        bins    sa          = (4 => 5 => 6), ([7:9],10=>11,12);
        bins    sb[]        = (4=> 5 => 6), ([7:9],10=>11,12);
        bins    sc          = (12 => 3 [-> 1]);
        bins    allother    = default sequence ;
    }
endgroup
```


## Coverage cross

A coverage group can specify cross coverage between two or more coverage points or variables. 
Cross coverage is specified using the cross construct. 
When a variable V is part of a cross coverage, 
SystemVerilog implicitly creates a coverage point for the variable, 
as if it had been created by the statement
`coverpoint V;`. 
Thus, a cross involves only coverage points. 
Expressions cannot be used directly in a cross; 
a coverage point must be explicitly defined first.

```
[cross_label: ]cross 
(<coverpoint_label> OR <variable_name>), (<coverpoint_label> OR <variable_name>)[, (<coverpoint_label> OR <variable_name>)]
[ iff (<iff_expression>)]
({(<cross_bins> OR <cross_options>)} OR ;)
```

Cross coverage of a set of N coverage points is defined as the coverage of all combinations of all bins 
associated with the N coverage points, that is, the Cartesian product of the N sets of coverage point bins. 
Cross coverage is allowed only between coverage points defined within the same coverage group. 


### Cross coverage bins

User-defined bins for cross coverage are defined using bin select expressions. 
The sytax is as following: 
```
bins OR ignored_bins OR illegal_bins 
=
<select_expression>
[ iff (<iff_expression>)]
```

User-defined cross bins and automatically generated bins can coexist in the same cross. 
Automatically generated bins are retained for those cross products 
that do not intersect cross products specified by any user-defined cross bin.

The `binsof` construct yields the bins of its expression. 
For example: 
```systemverilog
binsof (x) intersect {y}
```
denotes the bins of coverage point `x` whose values intersect the range given by `y`. 
```systemverilog
! binsof (x) intersect {y}
```
denotes the bins of coverage point `x` whose values do not intersect the range given by `y`. 

A user-defined corss coverage example: 
```systemverilog
bit [7:0] v_a, v_b;

covergroup cg @(posedge clk);
    a: coverpoint v_a
    {
        bins a1 = { [0:63] };
        bins a2 = { [64:127] };
        bins a3 = { [128:191] };
        bins a4 = { [192:255] };
    }

    b: coverpoint v_b
    {
        bins b1 = {0};
        bins b2 = { [1:84] };
        bins b3 = { [85:169] };
        bins b4 = { [170:255] };
    }

    c : cross a, b
    {
        //  <a1,b1>, <a1,b2>, <a1,b3>, and <a1,b4>
        bins c1 = ! binsof(a) intersect {[100:200]}; 
        //  <a2,b1>, <a2,b2>, <a2,b3>, <a2,b4>, <a1,b2>, <a3,b2>, and <a4,b2>
        bins c2 = binsof(a.a2) || binsof(b.b2); 
        //  <a1,b4>
        bins c3 = binsof(a.a1) && binsof(b.b4); 

        //  cross retains those automatically generated bins 
        //  that represent cross products not intersecting any of the user-defined bins.
        //  <a3,b1>, <a4,b1>, <a3,b3>, <a4,b3>, <a3,b4>, and <a4,b4>
    }
endgroup
```

The `with` clause is used to select bins tuples with values satisfying `<with_condition>`. 
The `with` syntax is as following: 
```
<select_expression>
with (<with_condition>) 
[ matches <match_num>]
```

The optional `matches` clause specifies the selection policy. 
The `match_num` shall evaluate to a positive integer or `$`, 
representing the minimum number of satisfying **value tuples** required to select the candidate bin tuple. 
The `$` symbol specifies that all value tuples must satisfy the expression to select the candidate bin tuple. 
When the `matches` clause is omitted, the selection policy defaults to one.


## Coverage options

There are two types of options: 
for an **instance** of a covergroup and 
for the covergroup **type** as a whole.

Cover option can be set within a `covergroup`, a `coverpoint` or a `cross`.  
A coverage option specified at the covergroup level applies to all of its items unless overridden by them.


### Instance-specific covergroup options

Instance-specific covergroup options include: 
- `name`
- `weight`, weight for coverage calculation, default is 1. 
- `goal`, coverage goal, default is 100. 
- `comment`, default is `""`
- `at_least`, minimum number of hits for each bin, default is 1. 
    A bin with a hit count that is less than number is not considered covered.
- `auto_bin_max`, maximum number of automatically created bins 
    when no bins are explicitly defined for a coverpoint, default is 64.
- `cross_num_print_missing`, number of not covered cross product bins 
    that shall be saved to the coverage database and printed in the coverage report, 
    default is 0. 
- `detect_overlap`, when true, a warning is issued if there is an overlap between the
    range list (or transition list) of two bins of a coverpoint, default is 0. 
- `per_instance`, default is 0. When true, 
    coverage information for this covergroup instance shall be saved in the coverage database 
    and included in the coverage report. 
    When false, implementations are not required to save instance-specific information.
- `get_inst_coverage`, 

An example for coverage options: 
```systemverilog
covergroup g1 (int w, string instComment) @(posedge clk) ;
    // track coverage information for each instance of g1 in addition
    // to the cumulative coverage information for covergroup type g1
    option.per_instance = 1;

    // comment for each instance of this covergroup
    option.comment = instComment;

    a : coverpoint a_var
    {
        // Create 128 automatic bins for coverpoint “a” of each instance of g1
        option.auto_bin_max = 128;
    }

    b : coverpoint b_var
    {
        // This coverpoint contributes w times as much to the coverage of an
        // instance of g1 as coverpoints "a" and "c1"
        option.weight = w;
    }

    c1 : cross a_var, b_var ;
endgroup
```

### Type-specific covergroup options

Type-specific covergroup options include: 
- `weight`, 
- `goal`, 
- `comment`, 
- `strobe`, default is 0.
    When true, all samples happen at the end of the time slot, 
    like the $strobe system task.
- `merge_instances`, default is 0. 
    When true, cumulative (or type) coverage is computed by merging instances together 
    as the union of coverage of all instances. 
    When false, type coverage is computed as the weighted average of instances.
- `distribute_first`, default is 0. 
    When true, instructs the tool to perform value distribution to the bins 
    prior to application of the `with_covergroup_expression`.

An example: 
```systemverilog
covergroup g1 (int w, string instComment) @(posedge clk) ;
    // track coverage information for each instance of g1 in addition
    // to the cumulative coverage information for covergroup type g1
    option.per_instance = 1;

    type_option.comment = "Coverage model for features x and y";

    type_option.strobe = 1; // sample at the end of the time slot

    // compute type coverage as the merge of all instances
    type_option.merge_instances = 1;

    // comment for each instance of this covergroup
    option.comment = instComment;

    a : coverpoint a_var
    {
        // Use weight 2 to compute the coverage of each instance
        option.weight = 2;
        // Use weight 3 to compute the cumulative (type) coverage for g1
        type_option.weight = 3;
        // NOTE: type_option.weight = w would cause syntax error.
    }

    b : coverpoint b_var
    {
        // Use weight w to compute the coverage of each instance
        option.weight = w;
        // Use weight 5 to compute the cumulative (type) coverage of g1
        type_option.weight = 5;
    }
endgroup
```

In the preceding example, the coverage for each instance of g1 is computed as follows: 
$$
\frac{(((instance\ coverage\ of\ a) \times 2) + ((instance\ coverage\ of\ b) \times w))}
{w + 2}
$$

On the other hand, the coverage for covergroup type g1 is computed as follows: 
$$
\frac{(((coverage\ merge\ from\ all\ instances) \times 3) + 
((coverage\ merge\ from\ all\ b\ instances) \times 5))}
{3 + 5}
$$


## Coverage tasks and functions

### Covergroup type methods

|Method                                         |Description                                                |
|:---                                           |:---                                                       |
|`void sample()`                                |Trigger sampling of the covergroup                         |
|`real get_coverage()`                          |Calculates **type** coverage number                        |
|`real get_coverage(ref int, ref int)`          |return covered bins number and total bins number as well   |
|`real get_inst_coverage()`                     |Calculates **inst** coverage number                        |
|`real get_inst_coverage(ref int, ref int)`     |return covered bins number and total bins number as well   |
|`void set_inst_name(string)`                   |Set the instance name to the given string                  |
|`void start()`                                 |Starts collecting coverage information                     |
|`void stop()`                                  |Stops collecting coverage information                      |

The `get_coverage()` method returns the or type coverage, 
which considers the contribution of all instances of a particular coverage item; 
and it is a static method that is available on both types (via the `::` operator) 
and instances (using the `.` operator). 

The `get_inst_coverage()` method returns the coverage of the specific instance on which it is invoked; 
thus, it can only be invoked via the `.` operator.


### Coverage system tasks and functions

Coverage system tasks and functions help to manage coverage data collection: 
- `$set_coverage_db_name(<file_name>)`, 
    sets the file name of the coverage database. 
- `$load_coverage_db(<file_name>)`, 
    loads coverage information from the given file name. 
- `$get_coverage`, 
    returns a real number of overall coverage of all covergroup types. 


## Coverage computation

Coverage of a coverpoint: 
$$
C_i = \frac{|bins_{covered}|}{|bins_{valid}|}
$$

For automatic bins, 
the $bins_{valid}$ is the minimum between the `auto_bin_max` or the $2^{M}$, 
where $M$ is the bit number needed to represent the coverpoint. 

Coverage of a coverage group: 
$$
C_g = \frac{\sum_{i} W_i \times C_i }{\sum_{i} W_i}
$$

The $C_i$ is the coverage of `coverpoint` or `cross`. 
The $W_i$ is the weight. 

Type coverage: 
$$
C_t = \frac{\sum_{i} W_i \times I_i }{\sum_{i} W_i}
$$


# Program

All statements within a program block are scheduled in reactive regions during simulation. 

```
program <program_name> [(<list_of_port>)];
    <program_contents>
endprogram
```

A program block may contain one or more `initial` or `final` procedures. 
`always` procedures are not allowed in program, 
which could be replaced by `forever` statement.

When all initial procedures within a program have reached their end, 
that program shall immediately terminate by means of an implicit call to `$finish`.

Elements within a program block is invisible to modules, 
which insures the independency of program as a testbench. 


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

```systemverilog
interface simple_bus (input logic clk); // Define the interface
    logic req, gnt;
    logic [7:0] addr, data;
    logic [1:0] mode;
    logic start, rdy;
endinterface: simple_bus

module memMod(simple_bus a); // Uses just the interface
    logic avail;

    always @(posedge a.clk) // the clk signal from the interface
        a.gnt <= a.req & avail; // a.req is in the 'simple_bus' interface
endmodule

module cpuMod(simple_bus b);
...
endmodule

module top;
    logic clk = 0;

    simple_bus sb_intf1(clk); // Instantiate the interface
    simple_bus sb_intf2(clk); // Instantiate the interface

    memMod mem1(.a(sb_intf1)); // Reference simple_bus 1 to memory 1
    cpuMod cpu1(.b(sb_intf1));
    memMod mem2(.a(sb_intf2)); // Reference simple_bus 2 to memory 2
    cpuMod cpu2(.b(sb_intf2));
endmodule
```

generic interface reference is used to declare an unspecified interface for later instantiate. 
the generic interface reference can only be declared using the ANSI style, 
which means the `interface` keyword must be explictly given in the port list. 

```systemverilog
interface simple_bus (input logic clk); // Define the interface
    logic req, gnt;
    logic [7:0] addr, data;
    logic [1:0] mode;
    logic start, rdy;
endinterface: simple_bus

module memMod(interface a); // Uses just the interface
    logic avail;

    always @(posedge a.clk) // the clk signal from the interface
        a.gnt <= a.req & avail; // a.req is in the 'simple_bus' interface
endmodule

module cpuMod(interface b);
...
endmodule

module top;
    logic clk = 0;

    simple_bus sb_intf1(clk); // Instantiate the interface
    simple_bus sb_intf2(clk); // Instantiate the interface

    memMod mem1(.a(sb_intf1)); // Reference simple_bus 1 to memory 1
    cpuMod cpu1(.b(sb_intf1));
    memMod mem2(.a(sb_intf2)); // Reference simple_bus 2 to memory 2
    cpuMod cpu2(.b(sb_intf2));
endmodule
```


## Modport

`modport` is used to indicate the directions during port declarations within interface. 
As the name indicates, the directions are those **seen from the module**. 

```
modport <modport_name> (<direction> <port_name>[, <direction> <port_name>])
```

A modport expression allows elements declared in an interface to be included in a modport list. 
Suppose an interface with modport is declared as: 

```systemverilog
interface i2;
    wire a, b, c, d;
    modport master (input a, b, output c, d);
    modport slave (output a, b, input c, d);
endinterface
```

Then it can be instantiated as: 

```systemverilog
module m (i2 i);
    ...
endmodule

module s0 (interface i);
    ...
endmodule

module s1 (i2.slave i);
    ...
endmodule

module top;
    i2 i();
    m   u1(.i     (i.master   ));
    s0  u2(.i     (i.slave    ));
    s1  u2(.i     (i          ));

endmodule
```

The modport construct can also be used to specify 
the direction of clocking blocks declared within an interface.
All of the clocking blocks used in a modport declaration shall be declared 
by the same interface as the modport itself.
Like all modport declarations, 
the direction of the clocking signals are those seen 
from the module in which the interface becomes a port.

An interface with a clock block and modports is declared and instantiated as: 

```systemverilog
interface A_Bus( input logic clk );
    wire req, gnt;
    wire [7:0] addr, data;

    clocking cb @(posedge clk);
        input gnt;
        output req, addr;
        inout data;
        property p1; 
            req ##[1:3] gnt; 
        endproperty
    endclocking

    modport DUT ( input clk, req, addr, // Device under test modport
        output gnt,
        inout data );
        
    modport STB ( clocking cb ); // synchronous testbench modport

    modport TB ( input gnt, // asynchronous testbench modport
        output req, addr,
        inout data );
endinterface

module dev1(A_Bus.DUT b); // Some device: Part of the design
    ...
endmodule

module dev2(A_Bus.DUT b); // Some device: Part of the design
    ...
endmodule

module top;
    logic clk;

    A_Bus b1( clk );
    A_Bus b2( clk );

    dev1 d1( b1 );
    dev2 d2( b2 );
    T tb( b1, b2 );
endmodule

program T (A_Bus.STB b1, A_Bus.STB b2 ); // testbench: 2 synchronous ports
    assert property (b1.cb.p1); // assert property from within program

    initial begin
        @b1.cb

        b1.cb.req <= 1;
        wait( b1.cb.gnt == 1 );
        ...
        b1.cb.req <= 0;
        b2.cb.req <= 1;
        wait( b2.cb.gnt == 1 );
        ...
        b2.cb.req <= 0;
    end
endprogram
```


