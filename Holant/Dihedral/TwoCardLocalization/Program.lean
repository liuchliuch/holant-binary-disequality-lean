import Holant.Dihedral.TwoCardLocalization.CoreStep

/-! Finite programs closing only residual ports. The ancestor is used once,
and exactly one fixed actual binary is used per instruction. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant
variable {K I : Type*} [Field K]

inductive Program (I : Type*) : ℕ → ℕ → Type _
  | done (n : ℕ) : Program I n n
  | step {n m : ℕ} (order : Equiv.Perm (Fin (n+2))) (label : I)
      (rest : Program I n m) : Program I (n+2) m

def Program.length {n m : ℕ} : Program I n m → ℕ
  | .done _ => 0
  | .step _ _ rest => rest.length+1

def Program.residual (C : I → Kernel K) {n m : ℕ} : Program I n m → Signature K n → Signature K m
  | .done _,q => q
  | .step p i rest,q => rest.residual C (Signature.contract (C i) (Tensor.reindex p.symm q))

def Program.core (C : I → Kernel K) {n m : ℕ} : Program I n m → Signature K (n+2) → Signature K (m+2)
  | .done _,q => q
  | .step p i rest,q => rest.core C (outsideClose p (C i) q)

/-- The exact representative count is one half the number of removed ports. -/
theorem Program.port_count {n m : ℕ} (P : Program I n m) : n=m+2*P.length := by
  induction P with
  | done n => simp [Program.length]
  | step p i rest ih => simp only [Program.length]; omega

/-- Both selected cards commute with the SAME recorded original-core program. -/
theorem Program.inherited_card (C : I → Kernel K) {n m : ℕ} (P : Program I n m)
    (A : Kernel K) (q : Signature K (n+2)) :
    Signature.contract A (P.core C q)=P.residual C (Signature.contract A q) := by
  induction P with
  | done n => rfl
  | step p i rest ih =>
    simp only [Program.core,Program.residual,ih,outside_card]

@[simp] theorem Program.core_smul (C : I → Kernel K) {n m : ℕ} (P : Program I n m)
    (c : K) (q : Signature K (n+2)) : P.core C (c • q)=c • P.core C q := by
  induction P with
  | done n => rfl
  | step p i rest ih =>
    simp only [Program.core]
    have h : outsideClose p (C i) (c • q)=c • outsideClose p (C i) q := by
      change Signature.contract (C i) (c • Tensor.reindex (outsideOrder p).symm q)=_
      rw [contract_smul]
      rfl
    rw [h,ih]

/-- A derived realization of the program, using only its original ancestor and
one actual fixed representative for each recorded label. The possible circle
and representative scalars accumulate into an explicit nonzero total scalar. -/
theorem Program.realizes_core (F : SignatureFamily K) (C B : I → Kernel K)
    (κ : I → K) (hκ : ∀ i,κ i ≠ 0)
    (hB : ∀ i,Gadget.Realizes F .disequality (binarySignature (B i)))
    (hentries : ∀ i a b,B i (!a) (!b)=κ i*C i a b) (htwo : (2:K) ≠ 0)
    {n m : ℕ} (P : Program I n m) (q : Signature K (n+2))
    (hq : Gadget.Realizes F .disequality q) :
    ∃ c : K,c ≠ 0 ∧ Gadget.Realizes F .disequality (c • P.core C q) := by
  induction P with
  | done n => exact ⟨1,one_ne_zero,by simpa [Program.core] using hq⟩
  | step p i rest ih =>
    obtain ⟨c,hc,hn,hr⟩ := actual_outside_step F q hq p (C i) (B i) (κ i) (hκ i) (hB i) (hentries i) htwo
    obtain ⟨d,hd,hout⟩ := ih ((c*κ i) • outsideClose p (C i) q) hr
    refine ⟨d*(c*κ i),mul_ne_zero hd hn,?_⟩
    simpa only [Program.core_smul,smul_smul,Program.core] using hout

/-- Shared finite induction for two-card invariants. The mathematical one-step
lemmas in the matching branches supply the displayed step, while this theorem
records all chosen literal ports and labels and proves the exact length. -/
theorem reduce_invariant (C : I → Kernel K)
    (Good : (n : ℕ) → Signature K n → Signature K n → Prop)
    (step : ∀ r (q₀ q₁ : Signature K (2*(r+1)+4)), Good _ q₀ q₁ →
      ∃ p : Equiv.Perm (Fin (2*(r+1)+4)), ∃ i : I,
        Good (2*r+4) (Signature.contract (C i) (Tensor.reindex p.symm q₀))
          (Signature.contract (C i) (Tensor.reindex p.symm q₁)))
    (r : ℕ) (q₀ q₁ : Signature K (2*r+4)) (h : Good _ q₀ q₁) :
    ∃ P : Program I (2*r+4) 4, P.length=r ∧ Good 4 (P.residual C q₀) (P.residual C q₁) := by
  induction r with
  | zero => exact ⟨.done 4,rfl,h⟩
  | succ r ih =>
    obtain ⟨p,i,hstep⟩ := step r q₀ q₁ h
    obtain ⟨P,hP,hout⟩ := ih _ _ hstep
    exact ⟨.step p i P,by simp [Program.length,hP],hout⟩

end Holant.Dihedral.TwoCardLocalization
