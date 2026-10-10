import Holant.Proofs.Reductions.FactorSaturation.Catalogue


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FactorSaturation
open Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction
open GeneralPowerExposure
variable {s : ℕ}
variable (roots : Fin s → AnySignature AlgebraicComplex) (hn : ∀ i, (roots i).2 ≠ 0)
variable (hI : RetainsIdentity (Set.range roots))

include hI
theorem power_exists (j : Fin (addedCount roots hn)) :
    Nonempty (PowerMacro (original roots hn) (next roots hn j.val)) := by
  change Nonempty (PowerMacro (original roots hn) (lookup roots hn (s+j.val)).2)
  rw [lookup_new]
  let u := enumerate roots hn j
  obtain ⟨b, ⟨q⟩⟩ := proper_split (tree roots hn u.1) u.2
  have hI' : RetainsIdentity (Set.range (fun i : Fin s =>
      (⟨arity roots hn i.val, original roots hn i⟩ : AnySignature AlgebraicComplex))) := by
    rw [original_family]
    exact hI
  apply q.left_power_labelled (original roots hn) hI' (by norm_num)
    (mixedSupport_of_identity _ hI') (hn u.1)
  apply Gadget.realizes_of_mem
  rw [original_family]
  exact ⟨u.1,rfl⟩

def power (j : Fin (addedCount roots hn)) : PowerMacro (original roots hn) (next roots hn j.val) :=
  Classical.choice (power_exists roots hn hI j)

/-- All normalization constants are attached to the finite stored occurrence
which caused the graph construction; no runtime carrier selection is needed. -/
theorem power_scale_nonzero (j : Fin (addedCount roots hn)) : (power roots hn hI j).scale ≠ 0 :=
  (power roots hn hI j).scale_ne_zero

end Holant.LocalDrafts.Hardness.FactorSaturation
