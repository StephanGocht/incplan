# incplan
Tool to do SAT Based Planning using an incremental SAT solver.

## Preparation
Get a sat solver implementing the ipasir api.
I.e. from http://baldur.iti.kit.edu/sat-race-2015/downloads/ipasir.zip
Drop the sat solver library implementing the ipasir api in lib/ipasir

## Building
cd build
cmake ../src
make

The binaries will now be in bin/