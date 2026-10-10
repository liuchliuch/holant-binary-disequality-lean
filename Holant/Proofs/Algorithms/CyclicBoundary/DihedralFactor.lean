import Holant.Proofs.Algorithms.CyclicBoundary.CrossedTables


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.DihedralFactor
open Holant.Projective.CyclicPhasePencil
noncomputable section

def anti (r : ℂ) : Kernel ℂ := fun u v => if u=v then 0 else if u then r else 1
def transfer (r : ℂ) : Kernel ℂ := Kernel.mul (anti r) Z

theorem transfer_square (r : ℂ) : Kernel.mul (transfer r) (transfer r) = (-r) • Signature.equality := by
  funext u v
  cases u <;> cases v <;>
    simp [transfer,anti,Z,diagonal,Kernel.mul,Signature.equality] <;> ring

theorem transfer_inverse (r : ℂ) (hr : r ≠ 0) :
    Kernel.mul (transfer r) ((-r)⁻¹ • transfer r) = Signature.equality ∧
      Kernel.mul ((-r)⁻¹ • transfer r) (transfer r) = Signature.equality := by
  constructor <;> funext u v <;> cases u <;> cases v <;>
    simp [transfer,anti,Z,diagonal,Kernel.mul,Signature.equality,hr]

theorem inverts_phase (r s : ℂ) (hs : s ≠ 0) :
    Kernel.mul (transfer r) (phase s) = s • Kernel.mul (phase (s⁻¹)) (transfer r) := by
  funext u v
  cases u <;> cases v <;>
    simp [transfer,anti,Z,phase,diagonal,Kernel.mul,hs] <;> ring

theorem conjugates_phase (r s : ℂ) (hr : r ≠ 0) (hs : s ≠ 0) :
    Kernel.mul (Kernel.mul (transfer r) (phase s)) ((-r)⁻¹ • transfer r) = s • phase (s⁻¹) := by
  funext u v
  cases u <;> cases v <;>
    simp [transfer,anti,Z,phase,diagonal,Kernel.mul,hr,hs] <;> ring

/-- The off-diagonal -1 entry already excludes every projective diagonal
phase. This is a statement about the actual ordered transfer Ar Z. -/
theorem outside_diagonal (r c s : ℂ) : transfer r ≠ c • phase s := by
  intro h
  have hh := congrArg (fun M : Kernel ℂ => M false true) h
  norm_num [transfer,anti,Z,phase,diagonal,Kernel.mul] at hh

theorem outside_cyclic (N : ℕ) (r : ℂ) : ¬IsPhase N (transfer r) := by
  rintro ⟨s,c,hs,hc,h⟩
  exact outside_diagonal r c s h

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.DihedralFactor
