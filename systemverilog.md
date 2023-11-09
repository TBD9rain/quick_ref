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

Data types are categorized as either singolar or aggregate. 
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


### 2-state variables

|Data Type  |Bit Width  |Default Range  |Description                        |
|:---       |:---       |:---           |:---                               |
|`bit`      |1          |unsigned       |could be used to make up vectors   |
|`int`      |32         |signed         |                                   |
|`byte`     |8          |signed         |                                   |
|`shortint` |16         |signed         |                                   |
|`longint`  |64         |signed         |                                   |


### String

`string` is a singular data type.
`string` data type is an ordered collection of characters. 
The length of a `string` variable is the number of characters in the collection. 
`string` variables are dynamic as their length may vary during simulation. 
A single character in a `string` variable could be selected. 
A single character in a `string` variable is of `byte`. 


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


### Structure

A structure represents a collection of data types that can be referenced as a whole, 
or the individual data types that make up the structure can be referenced by name.
By default, structures are unpacked, 
meaning that there is an implementation-dependent packing of the data types. 
Unpacked structures can contain any data type.

A packed structure consisits of bit fiels, which are packed together in memory without gaps.
An unpacked structure has an implementation-dependent packing, normally matching C compiler.
When a packed structure appears as a primary, it should be treated as a single vector.

