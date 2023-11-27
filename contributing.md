  # Contributing

Below is a list of tasks that need to be tackled. Mark tasks with `:hourglass_flowing_sand:⏳` for in progress, `:exclamation:❗` for need assistance and `:white_check_mark:✅` for finished, alongside your name(s) so that we can see who is working on what and avoid duplication of work. Please edit this file as necessary if tasks change or new ones are added!

* Formalisation
* Definitions/Imports (Jaime⏳)
* Define complex functions as $f(x, y)+ig(x, y)$ where $f$ and $g$ are real functions (or show they are equivalent to all functions $\omega: \mathbb{C} \rightarrow \mathbb{C}$)
* Consider the notion of "length" and how this relates to complex numbers ✅ (Jaime and Juan)
* Complex derivatives (could potentially define holomorphism) ✅ (Jaime and Juan)
* Complex (path) integrals
    * Define complex (path) integrals
    * Show additivity over the function ✅ (Jaime) AND over the path ⏳ (Jaime)
    * Show the Fundamental Theorem of Calculus for complex (path) integrals :white_check_mark: (Juan)
    * The following proof is significantly better/easier than the one in the notes (complex Cauchy-Schwartz): (It is in Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral.html#intervalIntegral.norm_integral_le_of_norm_le_const)
         https://math.stackexchange.com/a/4764147
        * Borrow the Cauchy-Schwartz inequality for real integrals :white_check_mark: (Mathlib - Edward)
        * Borrow the monotonicity of integrals
* Show that functions with antiderivatives have zero closed path integral (easy, by FTC) ✅ (Juan)

* Proof of Cauchy's Theorem (all subsections are independent):
    * Define triangles :white_check_mark: (Edward)
        * Can be defined as triplet of points, but realistically is much more useful as 3-set of vectors as there is more structure. Technically 3 colinear points is not a triangle but since it is trivial to show that Cauchy's Theorem holds in this case we will treat it anyway.
    * Define the set bounded by a triangle :white_check_mark: (Edward)
    * Show that the interior of a triangle is non-empty :hourglass_flowing_sand: (Juan) (It seems this would not be necessary to prove)
    * Define what it means to split up a triangle
    * Show that the sum of the inner triangles sum to the outer triangle
    * Show that at least one number is greater than or equal to the average of four numbers :white_check_mark: (Jaime)
    * Show there exists a limit of nested closed sets :white_check_mark: (Mathlib - Edward)
    * Show that the distance between two points in a triangle is less than the perimeter :white_check_mark: (Edward)
