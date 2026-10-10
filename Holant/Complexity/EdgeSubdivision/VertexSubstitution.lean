import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile
import Holant.Complexity.FixedGadgetSubstitution.Partition

/-! Fixed macro substitution with the caller's literal arity table. Arity
conversion changes no encoded byte and is justified by an exact table equality. -/
namespace Holant.Complexity.EdgeSubdivision.VertexSubstitution
open Computability BinaryCompose FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [CommSemiring K]
variable {sourceCount s b : ℕ} {inputArity arity : ℕ → ℕ}
variable (templates : ℕ → Template)
variable (he : sourceArity templates=inputArity)
variable (hg : ∀ i<sourceCount,(templates i).WellFormed s b arity)

include he hg in
theorem valid (r : RawClosedNetwork) (hr : r.WellFormed sourceCount b inputArity) :
    (replace templates r).WellFormed s b arity :=
  replace_wellFormed templates r hr (fun i hi => ⟨hg i hi,congrFun he i⟩)

def value (r : ExactSignatureTables.Input sourceCount b inputArity) :
    ExactSignatureTables.Input s b arity := ⟨replace templates r.val,valid templates he hg r.val r.property⟩

def computes : Computes (RawClosedNetwork.validatedEncoding sourceCount b inputArity)
    (RawClosedNetwork.validatedEncoding s b arity) (value templates he hg) := by
  subst inputArity
  exact FixedGadgetSubstitution.Compiler.computes sourceCount b (sourceArity templates)
    templates s arity (fun i hi => ⟨hg i hi,rfl⟩)

theorem partition (r : RawClosedNetwork) (hr : r.WellFormed sourceCount b inputArity)
    (source : (i : Fin sourceCount) → Signature K (inputArity i.val))
    (target : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K)
    (hlocal : ∀ i : Fin sourceCount,
      ((templates i.val).network (hg i.val i.isLt) target kernels).denote =
        (fun x => source i (fun j => x (Fin.cast (congrFun he i.val).symm j)))) :
    ((replace templates r).realize (valid templates he hg r hr) target kernels).denote Fin.elim0 =
      (r.realize hr source kernels).denote Fin.elim0 := by
  subst inputArity
  have hl : ∀ i : Fin sourceCount,
      ((templates i.val).network (hg i.val i.isLt) target kernels).denote = source i := by
    intro i
    simpa only [Fin.cast_refl,id_eq] using hlocal i
  have h := replacement_partition templates r hr hg source target kernels (fun _ => 1)
    (by intro i; simpa only [one_smul] using hl i)
  simpa using h

end
end Holant.Complexity.EdgeSubdivision.VertexSubstitution
