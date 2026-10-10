import Holant.ReedMuller.LowArity.Basic

namespace Holant.ReedMuller.LowArity.Dimension2
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def portTable : Fin 1 → Fin 1 → Fin 2 → Fin 2 := ![![![0,1]]]
def rawPorts (a : Fin 1) (p : Fin 1 × Fin 2) : Fin 2 := portTable a p.1 p.2
theorem rawPorts_bijective (a : Fin 1) : Function.Bijective (rawPorts a) := by
  fin_cases a <;> decide
noncomputable def model (a : Fin 1) : Matching 1 2 := Equiv.ofBijective (rawPorts a) (rawPorts_bijective a)

theorem model_orthogonal (a : Fin 1) :
    ∀ x y : BinaryVector 2, (model a).Holds x → (model a).Holds y → dot x y = 0 := by
  fin_cases a <;> decide

def proposal : Certificate (BinaryVector 2) (Fin 1) :=
  (.leaf 0)

theorem proposal_checked : check orth (fun a x => decide ((model a).Holds x))
    (Finset.univ.filter fun x => orth x x) proposal = true := by decide

theorem selfDual_matching (D : BinaryCode 2) (hD : SelfDual D) :
    ∃ a, ∀ x, x ∈ D ↔ (model a).Holds x :=
  selfDual_eq_matching model model_orthogonal proposal proposal_checked D hD

end Holant.ReedMuller.LowArity.Dimension2
