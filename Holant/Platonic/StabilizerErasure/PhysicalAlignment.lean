import Holant.Platonic.StabilizerErasure.AlignedForms
import Holant.Platonic.StabilizerErasure.CommutingPorts

/-! Compose exactly one genuine one-qubit axis Clifford at each physical
port. Distinct-port commutation proves simultaneous alignment, with no
assumed physical tableau or supplied coordinate-changing operator. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
open Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def axisFamilyProgram (p : Fin (n+1) → Fin 4) : List (Fin (n+1)) → Program (n+1)
  | [] => .identity
  | r::rs => .comp (axisProgram r (p r)) (axisFamilyProgram p rs)

theorem axisFamily_commutes (p : Fin (n+1) → Fin 4) (rs : List (Fin (n+1)))
    (r : Fin (n+1)) (hr : r∉rs) (R : Kernel ℂ) (f : Signature ℂ (n+1)) :
    (axisFamilyProgram p rs).run (siteAction r R f)=
      siteAction r R ((axisFamilyProgram p rs).run f) := by
  induction rs generalizing f with
  | nil => rfl
  | cons s rs ih =>
    have hsr : s≠r := by intro he;subst s;exact hr (by simp)
    have hrr : r∉rs := by intro he;exact hr (by simp [he])
    change (axisProgram s (p s)).run ((axisFamilyProgram p rs).run (siteAction r R f))=
      siteAction r R ((axisProgram s (p s)).run ((axisFamilyProgram p rs).run f))
    rw [ih hrr,axisProgram_exact,axisProgram_exact]
    exact siteAction_commute s r hsr _ _ _

theorem axisFamily_aligns (p : Fin (n+1) → Fin 4) (rs : List (Fin (n+1)))
    (hn : rs.Nodup) (r : Fin (n+1)) (hr : r∈rs) (hp : p r≠0)
    (f : Signature ℂ (n+1)) :
    (axisFamilyProgram p rs).run (siteAction r (qubitPauli (p r)) f)=
      siteAction r (qubitPauli 3) ((axisFamilyProgram p rs).run f) := by
  induction rs generalizing f with
  | nil => simp at hr
  | cons s rs ih =>
    obtain ⟨hs,hn⟩ := List.nodup_cons.mp hn
    change (axisProgram s (p s)).run
      ((axisFamilyProgram p rs).run (siteAction r (qubitPauli (p r)) f))=
      siteAction r (qubitPauli 3) ((axisProgram s (p s)).run ((axisFamilyProgram p rs).run f))
    rcases List.mem_cons.mp hr with hsr|hr
    · subst s
      rw [axisFamily_commutes p rs r hs]
      simp only [axisProgram_exact,siteAction_mul]
      rw [axisMatrix_intertwines (p r) hp]
    · have hsr : s≠r := by intro he;apply hs;simpa [he] using hr
      rw [ih hn hr,axisProgram_exact,axisProgram_exact]
      exact siteAction_commute s r hsr _ _ _

/-- This program contains one one-qubit Clifford at each physical port,
in a fixed order. Its factors commute because their ports are distinct. -/
def physicalAxisProgram (p : Fin (n+1) → Fin 4) : Program (n+1) :=
  axisFamilyProgram p (List.finRange (n+1))

theorem physicalAxisProgram_aligns (p : Fin (n+1) → Fin 4)
    (hp : ∀r,p r≠0) (r : Fin (n+1)) (f : Signature ℂ (n+1)) :
    (physicalAxisProgram p).run (siteAction r (qubitPauli (p r)) f)=
      siteAction r (qubitPauli 3) ((physicalAxisProgram p).run f) := by
  exact axisFamily_aligns p _ (List.nodup_finRange _) r (List.mem_finRange r) (hp r) f

end
end Holant.Platonic.StabilizerErasure
