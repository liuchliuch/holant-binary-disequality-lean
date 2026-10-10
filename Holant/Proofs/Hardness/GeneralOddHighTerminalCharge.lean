import Holant.Proofs.Hardness.GeneralOddUnaryOrdinary
import Mathlib.Data.Int.GCD

/-! Actual unary production from opposing coprime support charges.  Disjoint
copies and noncancelling pair contractions retain the original vertices.  The
integer equation selects numbers of copies, never a desired unary table.
This is a local producer, not the remaining whole-family hardness theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHighTerminalCharge
open Holant
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps NativeCopies
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n m : ℕ}

/-- Charge one reaches an actual unary.  The strengthened resource statement
counts every old internal edge and every new pair contraction. -/
theorem charge_one (F : SignatureFamily K) (htwo : (2 : K)≠0) (b : Bool)
    (N : Network K n) (hNF : Uses N F) (hNX : Native N)
    (x : Fin n → Bool) (hx : N.denote x≠0) (hb : balance b x=1) :
    ∃ U : Network K 1, Uses U F ∧ Native U ∧ U.denote (fun _ => b)≠0 ∧
      U.shape.vertices=N.shape.vertices ∧
      1+2*U.shape.edges=n+2*N.shape.edges := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hall : ∀ i,x i=b
    · have hn : n=1 := by
        have he : x=(fun _ => b) := funext hall
        simp [he,balance] at hb
        omega
      subst n
      exact ⟨N,hNF,hNX,(funext hall) ▸ hx,rfl,rfl⟩
    have hn : 2<n := by
      have hc := balance_count b x
      have hl := matches_le b x
      simp only [Fintype.card_fin] at hc hl
      by_contra hn
      have hone : n=1 := by omega
      apply hall
      have he := all_eq_of_card_le_balance b x (by simpa [hone,hb])
      exact congrFun he
    push_neg at hall
    obtain ⟨i,j,hij,y,hy,hby⟩ := exact_contraction htwo b N.denote x hx
      (by omega) (by simpa using hn) hall
    let C := (ofNetwork N).close i j hij
    let e := C.boundary
    let y' : Fin C.arity → Bool := fun a => y (e.symm a)
    have hcy : C.graph.denote y'≠0 := by
      change C.denote y≠0
      rw [Named.close_denote]
      exact hy
    have hbal : balance b y'=1 :=
      (balance_reindex e.symm b y).trans (hby.trans hb)
    have hc := remaining_card i j hij
    simp only [Fintype.card_fin] at hc
    have hlt : C.arity<n := by
      dsimp [C,Named.close]
      omega
    obtain ⟨U,hUF,hUX,hUb,hUv,hUe⟩ := ih C.arity hlt C.graph
      ((ofNetwork N).close_uses i j hij F hNF)
      ((ofNetwork N).close_native i j hij hNX) y' hcy hbal
    refine ⟨U,hUF,hUX,hUb,hUv,?_⟩
    have he : C.graph.shape.edges=N.shape.edges+1 := rfl
    have ha : C.arity+2=n := by dsimp [C,Named.close]; omega
    omega

/-- A bounded nonnegative Bezout equation.  In particular, no negative number
of occurrences or inverse signature is used by the graph construction. -/
theorem coprime_copies {q n : ℕ} (hn : 1<n) (hq : 0<q) (hcop : Nat.Coprime q n) :
    ∃ r s : ℕ, 0<r ∧ r<n ∧ s<q ∧ r*q=s*n+1 := by
  obtain ⟨r,hr,hmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn
  have he := Nat.mod_add_div (q*r) n
  rw [hmod] at he
  have heq : r*q=((q*r)/n)*n+1 := by nlinarith
  refine ⟨r,(q*r)/n,?_,hr,?_,heq⟩
  · by_contra hz
    have : r=0 := by omega
    simp [this] at hmod
  · have hmul : q*r<q*n := Nat.mul_lt_mul_of_pos_left hr hq
    nlinarith

theorem copies_edges (N : Network K n) (r : ℕ) :
    (copies N r).shape.edges=r*N.shape.edges := by
  induction r with
  | zero => simp [copies,Network.empty,NetworkShape.empty]
  | succ r ih =>
    rw [copies,Network.tensor_edges,ih]
    ring

/-- Real copies of two real graphs supply a charge-one word.  The product of
their actual supported coefficients is nonzero; all later cuts are physical
X edges.  The exact original port budget is retained. -/
theorem opposite_coprime (F : SignatureFamily K) (htwo : (2 : K)≠0) (b : Bool)
    (P : Network K m) (H : Network K n)
    (hPF : Uses P F) (hPX : Native P) (hHF : Uses H F) (hHX : Native H)
    (x : Fin m → Bool) (hx : P.denote x≠0)
    (hy : H.denote (fun _ => !b)≠0)
    (q : ℕ) (hq : 0<q) (hcharge : balance b x=q)
    (hn : 1<n) (hcop : Nat.Coprime q n) :
    ∃ r s : ℕ, 0<r ∧ r<n ∧ s<q ∧ r*q=s*n+1 ∧
      ∃ U : Network K 1, Uses U F ∧ Native U ∧ U.denote (fun _ => b)≠0 ∧
        U.shape.vertices=r*P.shape.vertices+s*H.shape.vertices ∧
        1+2*U.shape.edges=r*(m+2*P.shape.edges)+s*(n+2*H.shape.edges) := by
  obtain ⟨r,s,hr,hrn,hsq,he⟩ := coprime_copies hn hq hcop
  let N := (copies P r).tensor (copies H s)
  let w := appendWord (copyWord x r) (copyWord (fun _ : Fin n => !b) s)
  have hNF : Uses N F := tensor_uses F _ _ (copies_uses F P hPF r) (copies_uses F H hHF s)
  have hNX : Native N := tensor_native _ _ (copies_native P hPX r) (copies_native H hHX s)
  have hw : N.denote w≠0 := by
    rw [show N.denote w=P.denote x^r*H.denote (fun _ => !b)^s from by
      simp only [N,w,tensor_word,copies_word]]
    exact mul_ne_zero (pow_ne_zero r hx) (pow_ne_zero s hy)
  have hb : balance b w=1 := by
    simp only [w,balance_append,balance_copy,hcharge]
    have hc : balance b (fun _ : Fin n => !b)=-(n : ℤ) := by
      cases b <;> simp [balance]
    rw [hc]
    have hi : (r : ℤ)*q=(s : ℤ)*n+1 := by exact_mod_cast he
    linarith
  obtain ⟨U,hUF,hUX,hUb,hUv,hUe⟩ := charge_one F htwo b N hNF hNX w hw hb
  refine ⟨r,s,hr,hrn,hsq,he,U,hUF,hUX,hUb,?_,?_⟩
  · simpa [N,Network.tensor_vertices,copies_vertices] using hUv
  · simp only [N,Network.tensor_edges,copies_edges,copyArity_eq] at hUe
    nlinarith [hUe]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHighTerminalCharge
