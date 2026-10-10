import Holant.ReedMuller.DiagonalSlice.Source

/-! Regrouping literal card factors by their original logical coordinate.
Repeated coordinate labels are allowed and no factor-line assumption occurs. -/
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
variable {G E : Type*} [CommGroup G] [Fintype E] [DecidableEq E] {r : ℕ}

 theorem indexed_product_simple (h : (Fin r → Bool) → G) (i j : Fin r) (hij : i≠j)
    (c : G) (label : E → Fin r) (a : E → Bool → G)
    (hh : ∀x,x i=x j → h x=c*∏e,a e (x (label e))) : DiagonalSlice.SimpleDiagonal h i j := by
  classical
  let b : Fin r → Bool → G := fun k t => ∏e ∈ Finset.univ.filter (fun e=>label e=k),a e t
  have hprod (x : Fin r → Bool) : (∏k,b k (x k))=∏e,a e (x (label e)) := by
    calc
      _=∏k,∏e ∈ Finset.univ.filter (fun e=>label e=k),a e (x (label e)) := by
        apply Finset.prod_congr rfl
        intro k _
        apply Finset.prod_congr rfl
        intro e he
        rw [(Finset.mem_filter.mp he).2]
      _=_ := Finset.prod_fiberwise Finset.univ label (fun e=>a e (x (label e)))
  refine ⟨fun t=>c*b i t*b j t,b,?_⟩
  intro x hx
  rw [hh x hx,←hprod x]
  rw [←Finset.mul_prod_erase Finset.univ (fun k=>b k (x k)) (Finset.mem_univ i)]
  rw [←Finset.mul_prod_erase (Finset.univ.erase i) (fun k=>b k (x k))
    (by simp [Ne.symm hij] : j∈Finset.univ.erase i)]
  change c*(b i (x i)*(b j (x j)*(∏k∈DiagonalSlice.outside i j,b k (x k))))=_
  rw [←hx]
  group

end Holant.ReedMuller.WeightTwoIntegration
