\documentclass[english]{article} 
\usepackage[T1]{fontenc}
\usepackage[latin9]{inputenc}
\usepackage{amssymb} 
\usepackage{babel}
\textwidth = 500pt
\oddsidemargin=-1cm
\newcommand{\judges}{ \; \; \; \Gamma \vdash}

\begin{document}

\title{Korma Features} \author{Matthew Mirman}
\maketitle

\part*{Subtyping partial application with objects}


With ADTs, you can take a record with constructor name $N t_1 \cdots  t_n$
and it will corrospond to a function of type $t_1 \rightarrow \cdots \rightarrow t_n \rightarrow N$


Given that it is possible to continue adding values to an ADT, we would have operational semantics which would extend the values in a record if it were to be applied to another record with new, non overlapping records, ie, every record can be both a value and a function, being a primitive.  This wouldn't be so hard to accomplish, just check that when a record occurs, if the next thing on the stack is another record, you produce a new record containing both their, values. Standard garbage collection should take care of the problem where one's values are no longer needed

We add the following subtyping rule: 

Given $m \leq n \leq k \leq l$
$(S-PAPP)\frac{
   \judges t_m <: t'_m 
   \;\;\;\cdots
   \judges t_k <: t'_k  
}{
   \judges \{ r_1:t_1, \cdots , r_n:t_n\}     <:     \{ r_{n+1}:t_{n+1}, \cdots , r_{l}:t_{l} \} \rightarrow \{ r_m:t'_m, \cdots , r_{k}:t'_{k} \}
}$ 

We can clearly see that this rule is equivelent to the following:

$m \leq n \leq k \leq l$
$(S-PAPP)\frac{
   \judges \top  <: a \uparrow b
   \judges a \downarrow b <: c
}{
   \judges a  <: b  \rightarrow c
}$ 

However, are our semantics for the entire program validated safetly by this rule?  Should we ensure the progress theorem here?
I think we do not need to.  This is essentially a constant generating inference rule.  It basically means that all values can be treated
as constant functions, that append to information.


Extending the standard subtype inference algorithm to properly infer this rule is as simple as checking for it at the occurance of arrows and objects in unification,
and then performing the appropreate unification by checking that all the similarly named arguments subtype accordingly.

We use this with the following semantics: Given $n \leq k$

$(E-PAPP)\frac{
  \{ r_1=e_1, \cdots , r_n=e_n \} \;\; \{ r_{n+1}=e_{n+1}, \cdots , r_k=e_k\}
}{
  \{ r_1=e_1, \cdots , r_k=e_k\}
}$



\end{document}