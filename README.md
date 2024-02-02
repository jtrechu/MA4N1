# MA4N1 Project

Proving Cauchy's Theorem on a triangle using Gorsat's method

## Organisation of the file:

The file is divided into **7 folders** :

### Connection_with_mathlib

This folder contains files that lay out the equivalence between our code and the code that is already in Mathlib. This code only contains complex integrals over circular paths, and not arbitrary path.

### Definitions

This folder contains all definitions used for the project. This focuses mainly on paths (which has been defined in a separate way as in PathConnected), path integrals (which is a new structure based on the library IntervalIntegral) and triangles (which is also a new structure) among other definitions.

### Helpers

This folder contains a list of result that would be consider trivial on paper proofs. However they are not so trivial for Lean.

### Integral Zero

This folder contains 4 files (numbered in the logical order of the proof), they structure the proof to show that the integral is bounded by an arbitrarily small number.

### Lemmas

This folder contains all the lemmas used. Results that are not as important as the ones in the theorem folder.

### Old Files

This folder contains pieces of code that are no longer used, but pieces of it have been reused or updated. It also contains extra results we wanted to show, but weren't able to. 

### Theorem

This folder contains files with the more important results, as well as the main theorem we proved.

## Installation

Ensure that you have installed `lean4` and `lake`.
Clone the git repo.

Run 
```bash
lake update
lake exe cache get
```

And you are good to go!
## Contributing

All of your work uploaded here should fall under a specific task.
See `contributing.md` for the list of tasks and how to assign yourself that task.

