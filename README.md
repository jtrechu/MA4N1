# MA4N1 Project

Proving Cauchy's Theorem on a triangle using Gorsat's method

## Organisation of the file:

The file is divided into **7 folders** :

### Connection with Mathlib

This folder contains files that lay out the equivalence between our code and the code that is already in Mathlib. This code only contains complex integrals over circular paths, and not arbitrary path.

### Definitions

This folder contains all definitions used for the project. This focuses mainly on paths (which has been defined in a separate way as in PathConnected), path integrals (which is a new structure based on the library IntervalIntegral) and triangles (which is also a new structure) among other definitions.

### Helpers

This folder contains a list of result that would be consider trivial on paper proofs, or especially useful lemmas to unfold definitions. However they are not so trivial for Lean.

### Integral Zero

This folder contains 4 files (numbered in the logical order of the proof), they structure the proof to show that the integral is bounded by an arbitrarily small number.

### Lemmas

This folder contains all the lemmas used. Results that are used by the ones in the theorems folder, although they may be equally or harder to prove! Some notable results include:
- complex_ftc: The fundamental theorem of calculus for complex path integrals
- path_equalities & path_integral_linearity: Shows how we can compose and scale path integrals in different ways, on paths and integrand
- zero_le_of_gt_zero: a commonly-used result stating that a non-negative result bounded above by zero is zero
- integral_on_triangle: this result is central to our proof of Cauchy's theorem

### Old Files

This folder contains pieces of code that are no longer used, but pieces of it have been reused or updated. It also contains extra results we wanted to show, but weren't able to. 

### Theorem

This folder contains files with the more important results, as well as the main theorem we proved. Notable results include:
- cauchys_theorem_for_triangles: **the main result!** :partying_face:
- extended_cauchy: a very significant result, which is as the above but on a punctured domain
- triangle_topology: culminates proving that the interior of the triangle (as an explicit set) is equal to the definition of the interior of the triangular set. This result took some effort!

### Next steps

We were going to approximate a circleIntegral with a mesh of triangles, and use the intermediate theorem to prove the integral formula, but due to various difficulties along the way (such as the triangle topology, which was eventually proved) we did not manage to acheive this goal, however I am confident all the infrastructure is there.

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

