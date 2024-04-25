### Note about this directory

I have copied this modified version of an IMP parser from
https://github.com/zbruennig/z3-python

Who had previously copied it from 
https://github.com/DrkSephy/python-imp-interpreter
with the following comments

> None of the source code is mine; it is a subset of what is available at:
> 
> https://github.com/DrkSephy/python-imp-interpreter
> 
> I have made only small modifications to it for it to be more in line with a
> reaching analysis tool. Changes made are:
> 
> - Prevent evaluation of the AST. Once it creates the AST it simply returns it.
> 
> - Rename classes for simplicity and familiarity.
> 
> - Add skip statements

This directory is a basic IMP (the toy programming language) parser.
I have not currently made any modifications off of Zach Bruennigs changes.