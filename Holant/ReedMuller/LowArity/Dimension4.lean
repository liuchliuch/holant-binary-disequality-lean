import Holant.ReedMuller.LowArity.Basic

namespace Holant.ReedMuller.LowArity.Dimension4
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def portTable : Fin 3 → Fin 2 → Fin 2 → Fin 4 := ![![![0,1],![2,3]],![![0,2],![1,3]],![![0,3],![1,2]]]
def rawPorts (a : Fin 3) (p : Fin 2 × Fin 2) : Fin 4 := portTable a p.1 p.2
theorem rawPorts_bijective (a : Fin 3) : Function.Bijective (rawPorts a) := by
  fin_cases a <;> decide
noncomputable def model (a : Fin 3) : Matching 2 4 := Equiv.ofBijective (rawPorts a) (rawPorts_bijective a)

theorem model_orthogonal (a : Fin 3) :
    ∀ x y : BinaryVector 4, (model a).Holds x → (model a).Holds y → dot x y = 0 := by
  fin_cases a <;> decide

def proposal : Certificate (BinaryVector 4) (Fin 3) :=
  (.split (bits 4 12) (.leaf 0) (.split (bits 4 3) (.leaf 0) (.split (bits 4 10) (.leaf 1) (.split (bits 4 5) (.leaf 1) (.leaf 2)))))

theorem proposal_checked : check orth (fun a x => decide ((model a).Holds x))
    (Finset.univ.filter fun x => orth x x) proposal = true := by decide

theorem selfDual_matching (D : BinaryCode 4) (hD : SelfDual D) :
    ∃ a, ∀ x, x ∈ D ↔ (model a).Holds x :=
  selfDual_eq_matching model model_orthogonal proposal proposal_checked D hD

end Holant.ReedMuller.LowArity.Dimension4
