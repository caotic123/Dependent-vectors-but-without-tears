# Dependent-vectors-but-without-tears-.

![suprised](https://i.imgur.com/QeYRZXV.jpg)

*you when you are trying proving something with vector and get a weird problem*

Indexed lists sometimes can be tricky to figure out when you got a weird term in your proof.
This project aims a simply formalization of dependent vectors but including a set of theorems enough to you get free of 
your problems with dependent vectors.

There are some other formalizations and set of theorems about dependent vectors :
  
   - (the standard library of Vectors in Coq, VectorDef)

   - (Stdpp - A great extension of coq library, thanks Robbert, https://gitlab.mpi-sws.org/iris/stdpp)

Basically, the goal of this project is to be as simple as possible, that includes :

   - Doesn't use fin datatype (in my opinion is not useful to dependent vectors induction) 
   - Avoid maybe results
   - Use proofs in functions to make more easy reason about
   - Uses a lot of differents schemes induction 


Now, the library contains the functions of the standard library of coq and the most part of theorems in vector/stdpp.
If this library doesn't fit your project, I really recommend the stdpp library.


There are so many things to make vectors easier yet. So, anything creates an issue or a pull request.


Question or anything?
   camposferreiratiago@gmail.com