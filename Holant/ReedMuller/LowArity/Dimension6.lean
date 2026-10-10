import Holant.ReedMuller.LowArity.Basic

namespace Holant.ReedMuller.LowArity.Dimension6
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def portTable : Fin 15 → Fin 3 → Fin 2 → Fin 6 := ![![![0,1],![2,3],![4,5]],![![0,1],![2,4],![3,5]],![![0,1],![2,5],![3,4]],![![0,2],![1,3],![4,5]],![![0,2],![1,4],![3,5]],![![0,2],![1,5],![3,4]],![![0,3],![1,2],![4,5]],![![0,3],![1,4],![2,5]],![![0,3],![1,5],![2,4]],![![0,4],![1,2],![3,5]],![![0,4],![1,3],![2,5]],![![0,4],![1,5],![2,3]],![![0,5],![1,2],![3,4]],![![0,5],![1,3],![2,4]],![![0,5],![1,4],![2,3]]]
def rawPorts (a : Fin 15) (p : Fin 3 × Fin 2) : Fin 6 := portTable a p.1 p.2
theorem rawPorts_bijective (a : Fin 15) : Function.Bijective (rawPorts a) := by
  fin_cases a <;> decide
noncomputable def model (a : Fin 15) : Matching 3 6 := Equiv.ofBijective (rawPorts a) (rawPorts_bijective a)

theorem model_orthogonal (a : Fin 15) :
    ∀ x y : BinaryVector 6, (model a).Holds x → (model a).Holds y → dot x y = 0 := by
  fin_cases a <;> decide

def proposal : Certificate (BinaryVector 6) (Fin 15) :=
  (.split (bits 6 60) (.split (bits 6 51) (.leaf 0) (.split (bits 6 48) (.leaf 0) (.split (bits 6 15) (.leaf 0) (.split (bits 6 12) (.leaf 0) (.split (bits 6 43) (.leaf 1) (.split (bits 6 40) (.leaf 1) (.split (bits 6 23) (.leaf 1) (.split (bits 6 20) (.leaf 1) (.leaf 2))))))))) (.split (bits 6 51) (.split (bits 6 48) (.leaf 0) (.split (bits 6 15) (.leaf 0) (.split (bits 6 3) (.leaf 0) (.split (bits 6 46) (.leaf 11) (.split (bits 6 34) (.leaf 11) (.split (bits 6 29) (.leaf 11) (.split (bits 6 17) (.leaf 11) (.leaf 14)))))))) (.split (bits 6 48) (.split (bits 6 12) (.leaf 0) (.split (bits 6 3) (.leaf 0) (.split (bits 6 58) (.leaf 3) (.split (bits 6 53) (.leaf 3) (.split (bits 6 10) (.leaf 3) (.split (bits 6 5) (.leaf 3) (.leaf 6))))))) (.split (bits 6 15) (.split (bits 6 12) (.leaf 0) (.split (bits 6 3) (.leaf 0) (.split (bits 6 58) (.leaf 3) (.split (bits 6 53) (.leaf 3) (.split (bits 6 10) (.leaf 3) (.split (bits 6 5) (.leaf 3) (.leaf 6))))))) (.split (bits 6 12) (.split (bits 6 3) (.leaf 0) (.split (bits 6 46) (.leaf 11) (.split (bits 6 34) (.leaf 11) (.split (bits 6 29) (.leaf 11) (.split (bits 6 17) (.leaf 11) (.leaf 14)))))) (.split (bits 6 3) (.split (bits 6 43) (.leaf 1) (.split (bits 6 40) (.leaf 1) (.split (bits 6 23) (.leaf 1) (.split (bits 6 20) (.leaf 1) (.leaf 2))))) (.split (bits 6 58) (.split (bits 6 53) (.leaf 3) (.split (bits 6 10) (.leaf 3) (.split (bits 6 45) (.leaf 4) (.split (bits 6 40) (.leaf 4) (.split (bits 6 23) (.leaf 4) (.split (bits 6 18) (.leaf 4) (.leaf 5))))))) (.split (bits 6 53) (.split (bits 6 5) (.leaf 3) (.split (bits 6 46) (.leaf 10) (.split (bits 6 36) (.leaf 10) (.split (bits 6 27) (.leaf 10) (.split (bits 6 17) (.leaf 10) (.leaf 13)))))) (.split (bits 6 10) (.split (bits 6 5) (.leaf 3) (.split (bits 6 46) (.leaf 10) (.split (bits 6 36) (.leaf 10) (.split (bits 6 27) (.leaf 10) (.split (bits 6 17) (.leaf 10) (.leaf 13)))))) (.split (bits 6 5) (.split (bits 6 45) (.leaf 4) (.split (bits 6 40) (.leaf 4) (.split (bits 6 23) (.leaf 4) (.split (bits 6 18) (.leaf 4) (.leaf 5))))) (.split (bits 6 46) (.split (bits 6 36) (.leaf 10) (.split (bits 6 27) (.leaf 10) (.split (bits 6 34) (.leaf 11) (.split (bits 6 29) (.leaf 11) (.leaf 9))))) (.split (bits 6 40) (.split (bits 6 45) (.leaf 4) (.split (bits 6 18) (.leaf 4) (.split (bits 6 43) (.leaf 1) (.split (bits 6 20) (.leaf 1) (.leaf 9))))) (.split (bits 6 23) (.split (bits 6 45) (.leaf 4) (.split (bits 6 18) (.leaf 4) (.split (bits 6 43) (.leaf 1) (.split (bits 6 20) (.leaf 1) (.leaf 9))))) (.split (bits 6 17) (.split (bits 6 57) (.leaf 9) (.split (bits 6 6) (.leaf 9) (.split (bits 6 36) (.leaf 10) (.split (bits 6 27) (.leaf 10) (.leaf 11))))) (.split (bits 6 57) (.split (bits 6 54) (.leaf 6) (.split (bits 6 9) (.leaf 6) (.leaf 12))) (.split (bits 6 6) (.split (bits 6 54) (.leaf 6) (.split (bits 6 9) (.leaf 6) (.leaf 12))) (.split (bits 6 45) (.split (bits 6 33) (.leaf 14) (.split (bits 6 30) (.leaf 14) (.leaf 7))) (.split (bits 6 36) (.split (bits 6 39) (.leaf 2) (.split (bits 6 24) (.leaf 2) (.leaf 7))) (.split (bits 6 27) (.split (bits 6 39) (.leaf 2) (.split (bits 6 24) (.leaf 2) (.leaf 7))) (.split (bits 6 18) (.split (bits 6 54) (.leaf 7) (.split (bits 6 9) (.leaf 7) (.leaf 14))) (.split (bits 6 54) (.leaf 8) (.split (bits 6 9) (.leaf 8) (.split (bits 6 43) (.split (bits 6 34) (.leaf 8) (.split (bits 6 29) (.leaf 8) (.leaf 13))) (.split (bits 6 34) (.split (bits 6 20) (.leaf 8) (.leaf 5)) (.split (bits 6 29) (.split (bits 6 20) (.leaf 8) (.leaf 5)) (.split (bits 6 20) (.leaf 13) (.leaf 12)))))))))))))))))))))))))))

theorem proposal_checked : check orth (fun a x => decide ((model a).Holds x))
    (Finset.univ.filter fun x => orth x x) proposal = true := by decide

theorem selfDual_matching (D : BinaryCode 6) (hD : SelfDual D) :
    ∃ a, ∀ x, x ∈ D ↔ (model a).Holds x :=
  selfDual_eq_matching model model_orthogonal proposal proposal_checked D hD

end Holant.ReedMuller.LowArity.Dimension6
