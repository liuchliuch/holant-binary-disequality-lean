import Holant.ReedMuller.CoefficientAtlas.Geometry

/-! Multiplicative rigidity from actual normalized plane-slice products. -/
namespace Holant.ReedMuller.CoefficientAtlas
open scoped BigOperators
variable {G : Type*} [CommGroup G]

def CubeProducts (w : Param → G) : Prop :=
  ∀ p : Fin 28, ∀ t : Fin 3 → Bool,
    w (lift p t) = ∏ i, w (generators p i) ^ (if t i then 1 else 0 : ℕ)

theorem generators_product {w : Param → G} (h : CubeProducts w)
    (p : Fin 28) (i j : Fin 3) (hij : i≠j) :
    w (generators p i+generators p j)=w (generators p i)*w (generators p j) := by
  have H := h p (fun k => decide (k=i ∨ k=j))
  rw [lift_pair p i j hij] at H
  fin_cases i <;> fin_cases j <;> simp_all [Fin.prod_univ_three,mul_comm]
  all_goals exact mul_comm _ _

theorem plane_product {w : Param → G} (h : CubeProducts w)
    (a b : Param) (ha : Plane a) (hb : Plane b) (hab : a≠b) (hc : a+b≠oneParam) :
    w (a+b)=w a*w b := by
  obtain ⟨p,i,j,hij,rfl,rfl⟩ := plane_pair_covered a b ha hb hab hc
  exact generators_product h p i j hij

theorem plane_square {w : Param → G} (h : CubeProducts w) (a : Param) (ha : Plane a) :
    w a*w a=1 := by
  obtain ⟨b,hb,hab,hc⟩ := plane_companion a ha
  have hp := plane_product h a b ha hb hab hc
  have hsum := plane_sum a b ha hb hab hc
  have hne : a+b≠a := by
    intro he
    have hh := congrArg (fun z : Param => z+a) he
    rw [add_cancel,add_self_zero] at hh
    exact hb.1 hh
  have hp' := plane_product h (a+b) a hsum ha hne (by rw [add_cancel]; exact hb.2)
  rw [add_cancel,hp] at hp'
  have H : (w a*w a)*w b=1*w b := by
    calc
      _ = (w a*w b)*w a := by ac_rfl
      _ = w b := hp'.symm
      _ = _ := by simp
  exact mul_right_cancel H

theorem full_product {w : Param → G} (h : CubeProducts w) (p : Fin 28) :
    w oneParam=∏ i, w (generators p i) := by
  simpa only [lift_all,ite_true,pow_one] using h p (fun _ => true)

theorem one_square {w : Param → G} (h : CubeProducts w) : w oneParam*w oneParam=1 := by
  rw [full_product h 0,←Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  exact plane_square h _ (generators_plane 0 i)

theorem complement_product {w : Param → G} (h : CubeProducts w) (a : Param) (ha : Plane a) :
    w (oneParam+a)=w oneParam*w a := by
  obtain ⟨p,i,rfl⟩ := plane_occurs a ha
  have H := h p (fun j => decide (j≠i))
  rw [lift_complement] at H
  have he : (Finset.univ.filter fun j : Fin 3 => j≠i)=Finset.univ.erase i := by ext j; simp
  have hp : (∏ j, w (generators p j)^(if decide (j≠i) then 1 else 0 : ℕ))=
      ∏ j ∈ Finset.univ.erase i, w (generators p j) := by
    calc
      _ = ∏ j : Fin 3, if j≠i then w (generators p j) else 1 := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases hji : j≠i <;> simp [hji]
      _ = _ := by rw [←Finset.prod_filter,he]
  rw [hp] at H
  rw [H,full_product h p,←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [mul_assoc,plane_square h _ (generators_plane p i),mul_one]

theorem square {w : Param → G} (h0 : w 0=1) (h : CubeProducts w) (a : Param) : w a*w a=1 := by
  by_cases ha0 : a=0
  · simp [ha0,h0]
  by_cases ha1 : a=oneParam
  · rw [ha1]; exact one_square h
  exact plane_square h a ⟨ha0,ha1⟩

theorem multiplicative {w : Param → G} (h0 : w 0=1) (h : CubeProducts w) (a b : Param) :
    w (a+b)=w a*w b := by
  by_cases ha0 : a=0
  · simp [ha0,h0]
  by_cases hb0 : b=0
  · simp [hb0,h0]
  by_cases ha1 : a=oneParam
  · subst a
    by_cases hb1 : b=oneParam
    · subst b
      rw [add_self_zero,h0]
      exact (one_square h).symm
    · exact complement_product h b ⟨hb0,hb1⟩
  by_cases hb1 : b=oneParam
  · subst b
    rw [add_comm,mul_comm]
    exact complement_product h a ⟨ha0,ha1⟩
  by_cases hab : a=b
  · subst b
    rw [add_self_zero,h0]
    exact (plane_square h a ⟨ha0,ha1⟩).symm
  by_cases hc : a+b=oneParam
  · have hb : b=oneParam+a := by rw [←hc,add_cancel]
    rw [hc,hb,complement_product h a ⟨ha0,ha1⟩]
    calc
      w oneParam = w oneParam*(w a*w a) := by rw [plane_square h a ⟨ha0,ha1⟩,mul_one]
      _ = _ := by ac_rfl
  exact plane_product h a b ⟨ha0,ha1⟩ ⟨hb0,hb1⟩ hab hc

end Holant.ReedMuller.CoefficientAtlas
