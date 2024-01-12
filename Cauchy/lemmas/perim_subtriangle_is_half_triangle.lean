import Mathlib.Data.Set.Basic
import Cauchy.definitions.subtriangle
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Cauchy.definitions.triangle
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Init.Data.Float

open definitions
namespace lemmas


lemma perim_subtriangleA_is_half_triangle {T : Triangle}
  : perimeter (subTriangleA T) = ( perimeter T)/2 := by
  have h_sTa_eq_Ta : (subTriangleA T).toTriangle.a = T.a := by
    unfold subTriangleA
    unfold constructSubTriangle
    aesop


  have h_sTb_eq_half_Ta_plus_Tb : (subTriangleA T).toTriangle.b = T.a/2 + T.b/2 := by
    unfold subTriangleA
    unfold constructSubTriangle
    aesop

  have h_sTc_eq_half_Ta_plus_Tc : (subTriangleA T).toTriangle.c = T.a/2 + T.c/2 := by
    unfold subTriangleA
    unfold constructSubTriangle
    aesop

  have h_norm_2_is_2 : ‖(2 : ℂ)‖ = 2 := by aesop

  unfold perimeter
  rw[h_sTa_eq_Ta, h_sTb_eq_half_Ta_plus_Tb, h_sTc_eq_half_Ta_plus_Tc]
  repeat rw[dist_eq_norm]
  calc ‖T.a / 2 + T.b / 2 - T.a‖ + ‖T.a / 2 + T.c / 2 - (T.a / 2 + T.b / 2)‖ + ‖T.a - (T.a / 2 + T.c / 2)‖ = ‖(-T.a + T.b)/ 2‖ + ‖( T.c -  T.b) / 2‖ + ‖(T.a -  T.c) / 2‖ := by ring
  _ = ‖(-T.a + T.b)‖ / ‖(2 : ℂ)‖ + ‖( T.c -  T.b)‖ / ‖(2 : ℂ)‖ + ‖(T.a -  T.c)‖ / ‖(2 : ℂ)‖  := by repeat rw[norm_div]
  _ =  (‖T.b - T.a‖ + ‖T.c - T.b‖ + ‖T.a - T.c‖) / 2 := by repeat rw[h_norm_2_is_2]; ring

 lemma perim_subtriangleB_is_half_triangle {T : Triangle}
  : perimeter (subTriangleB T) = ( perimeter T)/2 := by
  have h_sTa_eq_half_Ta_plus_Tb : (subTriangleB T).toTriangle.a = T.a/2 + T.b/2 := by
    unfold subTriangleB
    unfold constructSubTriangle
    aesop


  have h_sTb_eq_Tb : (subTriangleB T).toTriangle.b = T.b := by
    unfold subTriangleB
    unfold constructSubTriangle
    aesop

  have h_sTc_eq_half_Tb_plus_Tc : (subTriangleB T).toTriangle.c = T.b/2 + T.c/2 := by
    unfold subTriangleB
    unfold constructSubTriangle
    aesop

  have h_norm_2_is_2 : ‖(2 : ℂ)‖ = 2 := by aesop

  unfold perimeter
  rw[h_sTa_eq_half_Ta_plus_Tb,  h_sTb_eq_Tb, h_sTc_eq_half_Tb_plus_Tc]
  repeat rw[dist_eq_norm]

  calc ‖T.b - (T.a / 2 + T.b / 2)‖ + ‖T.b / 2 + T.c / 2 - T.b‖ + ‖T.a / 2 + T.b / 2 - (T.b / 2 + T.c / 2)‖ = ‖(-T.a + T.b)/ 2‖ + ‖( T.c -  T.b) / 2‖ + ‖(T.a -  T.c) / 2‖ := by ring
  _ = ‖(-T.a + T.b)‖ / ‖(2 : ℂ)‖ + ‖( T.c -  T.b)‖ / ‖(2 : ℂ)‖ + ‖(T.a -  T.c)‖ / ‖(2 : ℂ)‖  := by repeat rw[norm_div]
  _ =  (‖T.b - T.a‖ + ‖T.c - T.b‖ + ‖T.a - T.c‖) / 2 := by repeat rw[h_norm_2_is_2]; ring

lemma perim_subtriangleC_is_half_triangle {T : Triangle}
  : perimeter (subTriangleC T) = ( perimeter T)/2 := by
  have h_sTa_eq_half_Ta_plus_Tc : (subTriangleC T).toTriangle.a = T.a/2 +T.c/2 := by
    unfold subTriangleC
    unfold constructSubTriangle
    aesop


  have h_sTb_eq_half_Tb_plus_Tc : (subTriangleC T).toTriangle.b = T.b/2 + T.c/2 := by
    unfold subTriangleC
    unfold constructSubTriangle
    aesop

  have h_sTc_eq_Tc : (subTriangleC T).toTriangle.c = T.c := by
    unfold subTriangleC
    unfold constructSubTriangle
    aesop

  have h_norm_2_is_2 : ‖(2 : ℂ)‖ = 2 := by aesop
  unfold perimeter
  rw[h_sTa_eq_half_Ta_plus_Tc, h_sTb_eq_half_Tb_plus_Tc, h_sTc_eq_Tc]
  repeat rw[dist_eq_norm]
  calc ‖T.b / 2 + T.c / 2 - (T.a / 2 + T.c / 2)‖ + ‖T.c - (T.b / 2 + T.c / 2)‖ + ‖T.a / 2 + T.c / 2 - T.c‖ = ‖(-T.a + T.b)/ 2‖ + ‖( T.c -  T.b) / 2‖ + ‖(T.a -  T.c) / 2‖ := by ring
  _ = ‖(-T.a + T.b)‖ / ‖(2 : ℂ)‖ + ‖( T.c -  T.b)‖ / ‖(2 : ℂ)‖ + ‖(T.a -  T.c)‖ / ‖(2 : ℂ)‖  := by repeat rw[norm_div]
  _ =  (‖T.b - T.a‖ + ‖T.c - T.b‖ + ‖T.a - T.c‖) / 2 := by repeat rw[h_norm_2_is_2]; ring

lemma perim_subtriangleD_is_half_triangle {T : Triangle}
  : perimeter (subTriangleD T) = ( perimeter T)/2 := by
  have h_sTa_eq_half_Ta_plus_Tb : (subTriangleD T).toTriangle.a = T.a/2 +T.b/2 := by
    unfold subTriangleD
    unfold constructSubTriangle
    aesop


  have h_sTb_eq_half_Tb_plus_Tc : (subTriangleD T).toTriangle.b = T.b/2 + T.c/2 := by
    unfold subTriangleD
    unfold constructSubTriangle
    aesop

  have h_sTc_eq_half_Ta_plus_Tc : (subTriangleD T).toTriangle.c = T.a/2 +T.c/2 := by
    unfold subTriangleD
    unfold constructSubTriangle
    aesop

  have h_norm_minus_2_is_2 : ‖(-2 : ℂ)‖ = 2 := by aesop
  unfold perimeter
  rw[h_sTa_eq_half_Ta_plus_Tb, h_sTb_eq_half_Tb_plus_Tc, h_sTc_eq_half_Ta_plus_Tc]
  repeat rw[dist_eq_norm]

  calc ‖T.b / 2 + T.c / 2 - (T.a / 2 + T.b / 2)‖ + ‖T.a / 2 + T.c / 2 - (T.b / 2 + T.c / 2)‖ + ‖T.a / 2 + T.b / 2 - (T.a / 2 + T.c / 2)‖= ‖( T.a - T.c)/ -2‖ + ‖( T.b - T.a ) / -2‖ + ‖(T.c - T.b) / -2‖ := by ring
  _ = ‖T.a - T.c‖ / ‖(-2 : ℂ)‖ + ‖(T.b - T.a )‖ / ‖(-2 : ℂ)‖ + ‖(T.c - T.b)‖ / ‖(-2 : ℂ)‖  := by repeat rw[norm_div]
  _ =  (‖ T.b - T.a‖  + ‖T.c - T.b‖ + ‖T.a - T.c‖) / 2 := by repeat rw[h_norm_minus_2_is_2]; ring
end lemmas
