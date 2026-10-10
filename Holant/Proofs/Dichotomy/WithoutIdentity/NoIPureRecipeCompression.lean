import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureRecipeTensor
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureCompressionSource

/-! Exact physical realization of any finite heterogeneous signed recipe
with zero modulo-four column charge. No analytic phase row is a resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureRecipeCompression
open Holant Holant.Complexity
open scoped BigOperators
namespace R
export NoIPurePhaseRecipeFactor (Port word incidence total)
end R
namespace T
export NoIPureRecipeTensor (output size ports incidence word_value)
end T
namespace C
export NoIPureCompressionSource (output value)
end C
namespace G
export NoIPureCompressionGraph (column signedWord)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {n m : ℕ}

def base (p : Fin n → R.Port m) (i : Fin n) : Bool :=
  match p i with
  | .inl _ => false
  | .inr (_,b) => b

def location (p : Fin n → R.Port m) (i : Fin n) : Bool ⊕ Fin m :=
  match p i with
  | .inl b => .inl b
  | .inr (j,_) => .inr j

theorem word_eq (p : Fin n → R.Port m) (z : Fin m → Bool) :
    G.signedWord (base p) (location p) z = R.word p z := by
  funext i
  cases h : p i with
  | inl b => simp [G.signedWord,base,location,R.word,h]
  | inr t => rcases t with ⟨j,b⟩; simp [G.signedWord,base,location,R.word,h]

theorem column_eq (p : Fin n → R.Port m) (j : Fin m) :
    G.column (base p) (location p) j = R.incidence p j := by
  unfold G.column R.incidence
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i with
  | inl b => simp [base,location,h]
  | inr t => rcases t with ⟨l,b⟩; simp [base,location,h]

variable {K : Type} [Field K] [Algebra ℚ K] {s k : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature K (a i.val))
variable (Q : NativeAntiTargetSource.Output H 4) (X : NativeAntiTargetSource.Output H 2)
variable (pins : Bool → NativeAntiTargetSource.Output H 1)
variable (qform : Q.network.denote = Holant.EightVertex.ProductAnchor.equalityFour)
variable (xform : X.network.denote = fun x => Signature.disequality (x 0) (x 1))
variable (pinform : ∀ b, (pins b).network.denote = fun x => if x 0=b then 1 else 0)
variable {ns : Fin k → ℕ}
variable (N : (v : Fin k) → NativeAntiTargetSource.Output H (ns v))
variable (ps : (v : Fin k) → Fin (ns v) → R.Port m)
variable (legal : ∀ j, R.total ps j % 4=0)

def output : NativeAntiTargetSource.Output H (m*2) :=
  C.output H Q X pins qform xform (T.output H N) (base (T.ports ps)) (location (T.ports ps))
    (fun j => by rw [column_eq,T.incidence]; exact legal j)

include pinform in
theorem value : (output H Q X pins qform xform N ps legal).network.denote =
    NoIPurePairedHardForm.paired (fun z => ∏ v, (N v).network.denote (R.word (ps v) z)) := by
  rw [output,C.value H Q X pins qform xform pinform]
  congr 1
  funext z
  rw [word_eq,T.word_value]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureRecipeCompression
end
