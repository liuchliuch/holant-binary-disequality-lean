import Holant.Certificates.PlatonicDeficient.OutputSemantics

/-! Literal nonzero pivots for scalar-aware adjoining.  The standard pivots
are rational.  The current O′ pivots are rational multiples of i. -/
namespace Holant.Certificates.PlatonicDeficient
open Holant Holant.Certificates.OctahedralSeparator
open Holant.Certificates.PlatonicQuaternaryExits.Deficient
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def outputPivot (p : Fin 6) : Fin 4 → Bool :=
  if p=2 ∨ p=3 then ![false,true,false,true] else ![false,false,true,true]
def outputPivotValue (p : Fin 6) : ℚ := if p=2 ∨ p=3 then -1/4 else 1/4

def primeOutputPivot : Fin 6 → Fin 4 → Bool :=
  ![![false,false,false,false],![false,true,false,true],![false,false,true,false],
    ![false,false,false,false],![false,true,false,false],![false,false,true,true]]
def primeOutputPivotValue : Fin 6 → ℚ := ![-1/128,1/64,-1/128,-1/128,-1/128,-1/64]

theorem output_pivot_scalar : ∀p : Fin 6,
    cachedBase (p.natAdd 9) (outputPivot p)=rat (outputPivotValue p) := by decide +kernel

theorem primeOutput_pivot_scalar : ∀p : Fin 6,
    primeTensor p (primeOutputPivot p)=coeff 0 0 (primeOutputPivotValue p) 0 := by
  intro p
  fin_cases p <;> decide +kernel

theorem outputPivotValue_ne_zero (p : Fin 6) : outputPivotValue p≠0 := by
  fin_cases p <;> norm_num [outputPivotValue]
theorem primeOutputPivotValue_ne_zero (p : Fin 6) : primeOutputPivotValue p≠0 := by
  fin_cases p <;> norm_num [primeOutputPivotValue]

noncomputable section

theorem output_pivot (p : Fin 6) : output p (outputPivot p)=(outputPivotValue p : ℂ) := by
  change embed (deficientCard p (outputPivot p))=_
  rw [←cached_deficient,output_pivot_scalar]
  simp [rat,embed_coeff]

theorem primeOutput_pivot (p : Fin 6) :
    primeOutput p (primeOutputPivot p)=(primeOutputPivotValue p : ℂ)*Complex.I := by
  change embed (primeTensor p (primeOutputPivot p))=_
  rw [primeOutput_pivot_scalar]
  simp [embed_coeff]

theorem output_pivot_ne_zero (p : Fin 6) : output p (outputPivot p)≠0 := by
  rw [output_pivot]
  exact_mod_cast outputPivotValue_ne_zero p

theorem primeOutput_pivot_ne_zero (p : Fin 6) : primeOutput p (primeOutputPivot p)≠0 := by
  rw [primeOutput_pivot]
  exact mul_ne_zero (by exact_mod_cast primeOutputPivotValue_ne_zero p) Complex.I_ne_zero

end
end Holant.Certificates.PlatonicDeficient
