[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# TeluMA - AIG Multiplier Examination Tool including Dual Variables
=====================================================================

Our tool TeluMA is able to verify and certify unsigned and signed
integer multipliers given as AIGs.

For further information we refer to the paper

Daniela Kaufmann, Paul Beame, Armin Biere, Jakob Nordström. 
 [`Adding Dual Variables to Algebraic Reasoning
for Gate-Level Multiplier Verification.`](https://danielakaufmann.at/kaufmannbeamebierenordstroem-date22/)
In Proc. Design, Automation and Test in Europe (DATE), 6 pages, 2022.

and the corresponding website http://fmv.jku.at/teluma  


INSTALL
--------------------------------------------------------------------
Use `./configure.sh && make` to configure and build `TeluMA`.

Furthermore, you need to have installed `gmp` to run `TeluMA`.


USAGE
--------------------------------------------------------------------
teluma <mode> <input.aig> <output files> [<option> ...] 

Depending on the <mode> <output files> have to be provided:


 mode = "-verify"
  
    <output files> =  no output files are required 
      
    <option> = the following options are available 
       -h | --help           print this command line summary 
       -v<1,2,3,4>           different levels of verbosity(default -v1) 
       -no-counter-examples  do not generate and write counter examples
     
     
 mode = "-certify"
  
    <output files> =  3 output files passed in the following order
      <out.polys>:      initial polynomial set 
      <out.proof>:      proof rules 
      <out.spec> :      spec which should be checked 
      
    <option> = the following options are available 
       -h | --help      print this command line summary 
       -v<1,2,3,4>      different levels of verbosity(default -v1) 
       -no-counter-examples  do not generate and write counter examples

       -p1          expanded proof 
       -p2          middle condensed proof(some linear combinations occur, default)
       -p3          condensed proof(one single linear combination);
