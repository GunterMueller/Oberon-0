# Purpose
This is an exercise in porting an excellent if obscure teaching tool to run on modern systems.

# Oberon-0
Oberon-0 is a simplified version of the language Oberon, conceived by Niklaus Wirth in 1986 as a refinement of his previous languages Pascal and Modula-2. It formed the basis of a complete computer and operating system, a number of which were networked and used at the ETH Zurich for many years.

The language itself is a study in refined minimalism, a strong but bare skeleton that still has a lot to teach modern language designers. In fact, it had a significant impact on the design of Google's Go programming language (golang.org).

# Porting
The Oberon-0 compiler specified in Nikluas Wirth's _Compiler Construction_ (www.ethoberon.ethz.ch/WirthPubl/CBEAll.pdf) is written to run on the ETH Zurich Oberon System. Not many of these exist in the wild these days, but there is a port of the language (without the operating system) still being maintained at Oxford University: the Oxford Oberon-2 compiler http://spivey.oriel.ox.ac.uk/corner/Installing_OBC_release_2.9

This is a port of the original source text of the compiler to Oxford Oberon-2, with any necessary changes made to get it to run. This is alpha code.

# Files
The original modules in the book were:
  - OSS.m : The scanner
  - OSP.m : The parser
  - OSG.m : The code generator
  - RISC.m : Emulator for virtual CPU

Only RISC.m is not included. The compiler will instead output an assembler listing.

# Running the project (Windows)
First install Oxford Oberon-2 v2.9.7. Next make sure you have the Oxford compiler install directory in your system PATH, so that typing 'obc' in any directory will run the compiler.

Build the project using the included quick lash-up "make.bat". Note: the source files all have a *.pas extension, this is to enable Pascal syntax highlighting in the text editor, but the compiler only accepts *.m extensions.

When built, it will start the Oxford Oberon debugger, necessary because without it, the virtual machine will crash with 
"Fatal error: fixr LOADQ". Push the RUN button and the Oberon-0 compiler will run, displaying the output to screen and to a file with the same name as the input file

To change the input file, edit make.bat.
