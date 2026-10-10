import Holant.Proofs.Hardness.ThreeModeChain
import Holant.Proofs.Hardness.EqualModulusThreeModeLocal

/-! A positive, fixed number of original q copies. The input exponent is the
original coefficient-field torsion bound in the closed factory. There are
exactly n rows and 2(n-1) native-X edges, with the frozen chain port order. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeChain
open Holant Holant.Complexity FixedGadgetSubstitution
namespace R
export ExactTwoChainRecords (explicitTemplate explicitRow vertices_length edges_length)
end R
variable {K : Type} [Field K] [CharZero K]

def first (a b : K) (n : ℕ) := ((a+b)^n-(b-a)^n)/2
def second (a b : K) (n : ℕ) := ((a+b)^n+(b-a)^n)/2
def third (c : K) (n : ℕ) := c^n

theorem sum (a b : K) (n : ℕ) : first a b n+second a b n=(a+b)^n := by
  unfold first second
  ring

theorem difference (a b : K) (n : ℕ) : second a b n-first a b n=(b-a)^n := by
  unfold first second
  ring

def template (n : ℕ) : Template := R.explicitTemplate 0 0 (n-1)
theorem valid (n : ℕ) : (template n).WellFormed 1 1 (fun _=>4) :=
  ExactTwoChainRecords.valid (fun _=>4) (0 : Fin 1) rfl (0 : Fin 1) (n-1)

theorem records (n : ℕ) (hn : 0<n) :
    (template n).boundary=4 ∧
    (template n).vertices=(List.range n).map (R.explicitRow 0 (n-1)) ∧
    (template n).edges=List.replicate (2*(n-1)) 0 := by
  simp only [template,R.explicitTemplate,show n-1+1=n by omega,and_self]

theorem counts (n : ℕ) (hn : 0<n) :
    (template n).vertices.length=n ∧ (template n).edges.length=2*(n-1) := by
  rw [template,R.vertices_length,R.edges_length]
  omega

theorem template_denote (a b c : K) (n : ℕ) (hn : 0<n) :
    ((template n).network (valid n) (fun _ : Fin 1=>ThreeModeSignatures.original a b c)
      (fun _ : Fin 1=>Signature.disequality)).denote=
      ThreeModeSignatures.original (first a b n) (second a b n) (third c n) := by
  have h := ThreeModeChain.denote (fun _=>4) (0 : Fin 1) rfl (0 : Fin 1)
    a b c (n-1) (fun _ : Fin 1=>ThreeModeSignatures.original a b c)
    (fun _ : Fin 1=>Signature.disequality) rfl rfl
  rw [show n-1+1=n by omega] at h
  exact h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeChain
