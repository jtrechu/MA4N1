  # Contributing

Below is a list of tasks that need to be tackled. Mark tasks with `:hourglass_flowing_sand:⏳` for in progress, `:exclamation:❗` for need assistance and `:white_check_mark:✅` for finished, alongside your name(s) so that we can see who is working on what and avoid duplication of work. Please edit this file as necessary if tasks change or new ones are added!

* Formalisation
* Definitions/Imports
* Define complex functions as $f(x)+ig(y)$ where $f$ and $g$ are real functions (or show they are equivalent to all functions $\omega: \mathbb{C} \rightarrow \mathbb{C}$)
* Consider the notion of "length" and how this relates to complex numbers
* Complex derivatives (could potentially define holomorphism)
* Complex (path) integrals
    * Define complex (path) integrals
    * Show additivity over the function AND over the path
    * Show the Fundamental Theorem of Calculus for complex (path) integrals 
    * The following proof is significantly better/easier than the one in the notes (complex Cauchy-Schwartz): https://math.stackexchange.com/a4764147
        * Borrow the Cauchy-Schwartz inequality for real integrals
        * Borrow the monotonicity of integrals
* Show that functions with antiderivatives have zero closed path integral (easy, by FTC)

* Proof of Cauchy's Theorem (all subsections are independent):
    * Define triangles ⏳ (Edward)
        * Can be defined as triplet of points, but realistically is much more useful as 3-set of vectors as there is more structure. Technically 3 colinear points is not a triangle but since it is trivial to show that Cauchy's Theorem holds in this case we will treat it anyway.
    * Show that the interior of a triangle is non-empty
    * Define what it means to split up a triangle
    * Show that the sum of the inner triangles sum to the outer triangle
    * Show that at least one number is greater than or equal to the average of four numbers ✅ (Jaime)
    * Show there exists a limit of nested closed sets
    * Show that the distance between two points in a triangle is less than the perimeter
