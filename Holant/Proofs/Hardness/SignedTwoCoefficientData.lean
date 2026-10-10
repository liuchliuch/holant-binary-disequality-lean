import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-! Signed scalar data shared by the actual two-copy quaternary gadget and the
finite ratio-escape proof. The ordered coefficients retain every actual sign. A stage is iteration of the exact same polynomial
coefficient map; no successful interpolation condition is stored in the data. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SignedTwoCoefficientData
variable {K : Type*}

def step [CommRing K] (p : K×K) : K×K := (-p.1*p.2,p.2*(p.1-p.2))
def stage [CommRing K] (a b : K) : ℕ → K×K
  | 0=>(a,b)
  | k+1=>step (stage a b k)

@[simp] theorem stage_zero [CommRing K] (a b : K) : stage a b 0=(a,b) := rfl
@[simp] theorem stage_succ [CommRing K] (a b : K) (k : ℕ) :
    stage a b (k+1)=step (stage a b k) := rfl
@[simp] theorem stage_one [CommRing K] (a b : K) : stage a b 1=(-a*b,b*(a-b)) := rfl

theorem stage_two [CommRing K] (a b : K) :
    stage a b 2=(a*b^2*(a-b),-b^2*(a-b)*(2*a-b)) := by
  apply Prod.ext <;> simp only [stage,step,Prod.fst,Prod.snd] <;> ring

def ratio [Field K] (p : K×K) : K := p.1/(-2*p.2)
def InfiniteRatio [Field K] (p : K×K) : Prop := ∀n : ℕ,0<n → (ratio p)^n≠1

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SignedTwoCoefficientData
