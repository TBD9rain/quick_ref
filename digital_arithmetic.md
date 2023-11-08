# Mathematical Notations 

|Symbols                |Description                            |
|:---                   |:---                                   |
|$\lceil n \rceil$      |the least integer not less than x      |
|$\lfloor n \rfloor$    |the largest integer not exceeding x    |


# Fixed-point 

Fixed-point is a method to represent sign, integer part, and fraction part of a number, 
with a fixed number of digits in format of binary data. 
The fixed-point numbers have specific and fixed precision. 

If a fixed-point mode is defined as following, 
then $100101100$ equals to $-26.5$ in decimal.
$$
\overbrace{0}^{sign}
\overbrace{00000}^{integer}
\overbrace{000}^{fraction}
$$


## General Division 



## Division by Invariant Integers

Variant integer dividents and invariant integer divisor 
can be **replaced by mulpilication and bit-shift**.


### Unsigned dividison

***Theorem***

Suppose $m$, $d$, $l$ are nonnegative integers, while $d \ne 0$ and:
$$
2^{N+l} \le m \times d \le 2^{N+l} + 2^l
$$
then for unsigned integer dividend $n$ and divisor $d$ 
with $0 \le n, d \le 2^{N}-1$ there is:
$$
\lfloor \frac n d \rfloor =
\lfloor \frac {m \times n} {2^{N+l}} \rfloor
$$


***Proof***


### Application

Matlab codes to calculate $m$ and $l$:
```matlab
% max bit width of divident and divisor
N = 32;
% divisor
d = 17;

l = ceil(log2(d));

low     = floor(2^(N + l) / d);
high    = floor((2^(N + l) + 2^l) / d);
shift_n = l;

while (floor(low / 2) < floor(high / 2) && shift_n > 0)
    low = floor(low / 2);
    high = floor(high / 2);
    shift_n = shift_n - 1;
end

m = high;
l = shift_n;
```


### Signed division, quotient rounded towards 0


### Signed division, quotient rounded towards $-\infin$


### Reference:

[Division by Invariant Integers using Multiplicaiton](https://dl.acm.org/doi/10.1145/178243.178249)


# Float-point

