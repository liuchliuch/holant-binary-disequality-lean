import Holant.Proofs.Hardness.GeneralOddHighTerminalSource

/-! Opposite support with charge not divisible by the actual high terminal's
arity yields a strictly smaller odd actual graph.  The terminal need not have
prime arity, and neither tensor-factor extraction nor hardness is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHighTerminalGcd
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps NativeCopies
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralOddUnaryOrdinary GeneralOddUnarySource
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n m : ℕ}

/-- Exact positive charge, with the entire old port budget retained. -/
theorem positive_charge (F : SignatureFamily K) (htwo : (2 : K)≠0) (b : Bool)
    (N : Network K n) (hNF : Uses N F) (hNX : Native N)
    (x : Fin n → Bool) (hx : N.denote x≠0) (d : ℕ) (hd : 0<d)
    (hb : balance b x=d) :
    ∃ U : Network K d, Uses U F ∧ Native U ∧ U.denote (fun _ => b)≠0 ∧
      U.shape.vertices=N.shape.vertices ∧
      d+2*U.shape.edges=n+2*N.shape.edges := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hall : ∀ i,x i=b
    · have hn : n=d := by
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
      apply hall
      have he := all_eq_of_card_le_balance b x (by simp only [Fintype.card_fin]; omega)
      exact congrFun he
    push Not at hall
    obtain ⟨i,j,hij,y,hy,hby⟩ := exact_contraction htwo b N.denote x hx
      (by omega) (by simpa using hn) hall
    let C := (ofNetwork N).close i j hij
    let e := C.boundary
    let y' : Fin C.arity → Bool := fun a => y (e.symm a)
    have hcy : C.graph.denote y'≠0 := by
      change C.denote y≠0
      rw [Named.close_denote]
      exact hy
    have hbal : balance b y'=d :=
      (balance_reindex e.symm b y).trans (hby.trans hb)
    have hc := remaining_card i j hij
    simp only [Fintype.card_fin] at hc
    have hlt : C.arity<n := by dsimp [C,Named.close]; omega
    obtain ⟨U,hUF,hUX,hUb,hUv,hUe⟩ := ih C.arity hlt C.graph
      ((ofNetwork N).close_uses i j hij F hNF)
      ((ofNetwork N).close_native i j hij hNX) y' hcy hbal
    refine ⟨U,hUF,hUX,hUb,hUv,?_⟩
    have he : C.graph.shape.edges=N.shape.edges+1 := rfl
    have ha : C.arity+2=n := by dsimp [C,Named.close]; omega
    omega

/-- Bounded positive-copy reduction to the proper gcd. -/
theorem gcd_copies {q n : ℕ} (hn : 0<n) (hq : 0<q) (hdiv : ¬n∣q) :
    0<Nat.gcd q n ∧ Nat.gcd q n<n ∧
      ∃ r s : ℕ, 0<r ∧ r<n ∧ s<q ∧ r*q=s*n+Nat.gcd q n := by
  have hd : 0<Nat.gcd q n := Nat.gcd_pos_of_pos_right q hn
  have hdn : Nat.gcd q n<n := by
    have hle := Nat.gcd_le_right q hn
    by_contra h
    have he : Nat.gcd q n=n := by omega
    exact hdiv (he ▸ Nat.gcd_dvd_left q n)
  obtain ⟨r,hr,hmod⟩ := Nat.exists_mul_mod_eq_gcd hdn
  have he := Nat.mod_add_div (q*r) n
  rw [hmod] at he
  have heq : r*q=((q*r)/n)*n+Nat.gcd q n := by nlinarith
  refine ⟨hd,hdn,r,(q*r)/n,?_,hr,?_,heq⟩
  · by_contra hz
    have : r=0 := by omega
    simp [this] at hmod
    omega
  · have hmul : q*r<q*n := Nat.mul_lt_mul_of_pos_left hr hq
    nlinarith

/-- The reduction includes every original coefficient and physical edge.
The output arity is the computed gcd, not a requested synthetic signature. -/
theorem native_reduction (F : SignatureFamily K) (htwo : (2 : K)≠0) (b : Bool)
    (P : Network K m) (H : Network K n)
    (hPF : Uses P F) (hPX : Native P) (hHF : Uses H F) (hHX : Native H)
    (x : Fin m → Bool) (hx : P.denote x≠0)
    (hy : H.denote (fun _ => !b)≠0)
    (q : ℕ) (hq : 0<q) (hcharge : balance b x=q) (hn : 0<n) (hdiv : ¬n∣q) :
    0<Nat.gcd q n ∧ Nat.gcd q n<n ∧
      ∃ r s : ℕ, 0<r ∧ r<n ∧ s<q ∧ r*q=s*n+Nat.gcd q n ∧
        ∃ U : Network K (Nat.gcd q n), Uses U F ∧ Native U ∧
          U.denote (fun _ => b)≠0 ∧
          U.shape.vertices=r*P.shape.vertices+s*H.shape.vertices ∧
          Nat.gcd q n+2*U.shape.edges=
            r*(m+2*P.shape.edges)+s*(n+2*H.shape.edges) := by
  obtain ⟨hd,hdn,r,s,hr,hrn,hsq,he⟩ := gcd_copies hn hq hdiv
  let N := (copies P r).tensor (copies H s)
  let w := appendWord (copyWord x r) (copyWord (fun _ : Fin n => !b) s)
  have hNF : Uses N F := tensor_uses F _ _ (copies_uses F P hPF r) (copies_uses F H hHF s)
  have hNX : Native N := tensor_native _ _ (copies_native P hPX r) (copies_native H hHX s)
  have hw : N.denote w≠0 := by
    rw [show N.denote w=P.denote x^r*H.denote (fun _ => !b)^s from by
      simp only [N,w,tensor_word,copies_word]]
    exact mul_ne_zero (pow_ne_zero r hx) (pow_ne_zero s hy)
  have hb : balance b w=Nat.gcd q n := by
    simp only [w,balance_append,balance_copy,hcharge]
    have hc : balance b (fun _ : Fin n => !b)=-(n : ℤ) := by
      cases b <;> simp [balance]
    rw [hc]
    have hi : (r : ℤ)*q=(s : ℤ)*n+Nat.gcd q n := by exact_mod_cast he
    linarith
  obtain ⟨U,hUF,hUX,hUb,hUv,hUe⟩ := positive_charge F htwo b N hNF hNX w hw _ hd hb
  refine ⟨hd,hdn,r,s,hr,hrn,hsq,he,U,hUF,hUX,hUb,?_,?_⟩
  · simpa [N,Network.tensor_vertices,copies_vertices] using hUv
  · simp only [N,Network.tensor_edges,GeneralOddHighTerminalCharge.copies_edges,
      copyArity_eq] at hUe
    nlinarith [hUe]

section Original
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)
open GeneralOddHighTerminalSource

/-- Every opposite original support charge not divisible by the actual high
terminal arity yields a smaller nonzero odd ordinary graph. -/
theorem source (hh : 3≤(result G j ho hnz).arity) (b : Bool)
    (hy : endpoint G j ho hnz (!b)≠0) (k : Fin s)
    (x : Fin (a k.val) → Bool) (hx : sourceKBasis.symm.action (G k) x≠0)
    (q : ℕ) (hq : 0<q) (hcharge : balance b x=q)
    (hdiv : ¬(result G j ho hnz).arity∣q) :
    let d := Nat.gcd q (result G j ho hnz).arity
    Odd d ∧ d<(result G j ho hnz).arity ∧
      ∃ r t : ℕ, 0<r ∧ r<(result G j ho hnz).arity ∧ t<q ∧
        r*q=t*(result G j ho hnz).arity+d ∧
        ∃ U : Network AlgebraicComplex d, Uses U (original G) ∧ Ordinary U ∧
          sourceKBasis.symm.action U.denote (fun _ => b)≠0 ∧ U.denote≠0 ∧
          U.shape.vertices=r+t ∧ d+2*U.shape.edges=r*a k.val+t*a j.val ∧
          U.shape.vertices≤a j.val+a k.val-2 := by
  let P := toNative (Network.corolla (G k))
  let H := toNative (high G j ho hnz)
  have hPF : Uses P (kCoordinates (original G)) :=
    toNative_uses (original G) _ (fun _ => ⟨k,rfl⟩)
  have hPX : Native P := toNative_native _ (fun e => Fin.elim0 e)
  have hHF : Uses H (kCoordinates (original G)) :=
    toNative_uses (original G) _ (high_uses G j ho hnz)
  have hHX : Native H := toNative_native _ (high_ordinary G j ho hnz)
  have hx' : P.denote x≠0 := by simpa [P,toNative_denote,Network.denote_corolla] using hx
  have hy' : H.denote (fun _ => !b)≠0 := by simpa [H,toNative_denote] using hy
  obtain ⟨hd,hdn,r,t,hr,hrn,htq,he,U,hUF,hUX,hUb,hUv,hUe⟩ :=
    native_reduction (kCoordinates (original G)) (by norm_num) b P H
      hPF hPX hHF hHX x hx' hy' q hq hcharge (by omega) hdiv
  have hodd : Odd (Nat.gcd q (result G j ho hnz).arity) :=
    Odd.of_dvd_nat (result G j ho hnz).odd (Nat.gcd_dvd_right _ _)
  have hdiag : sourceKBasis.symm.action (toOrdinary U).denote=U.denote := by
    rw [toOrdinary_denote,InvertibleKernel.symm_action_action]
  have hUnz : (toOrdinary U).denote≠0 := by
    intro hz
    have he := congrArg sourceKBasis.symm.action hz
    rw [hdiag] at he
    exact hUb (congrFun (he.trans (Signature.coordinateAction_zero _)) (fun _ => b))
  have hvertices : (toOrdinary U).shape.vertices=r+t := by
    change U.shape.vertices=r+t
    have hH : H.shape.vertices=1 := (result G j ho hnz).frame.one
    have hP : P.shape.vertices=1 := rfl
    simpa [hH,hP] using hUv
  have hecon := Loops.selected_conservation G j ho hnz
  have hedge : Nat.gcd q (result G j ho hnz).arity+2*(toOrdinary U).shape.edges=
      r*a k.val+t*a j.val := by
    change Nat.gcd q (result G j ho hnz).arity+2*U.shape.edges=_
    have hP : P.shape.edges=0 := rfl
    have hH : H.shape.edges=(result G j ho hnz).frame.shape.edges := rfl
    simpa only [hP,hH,Nat.mul_zero,Nat.add_zero,hecon] using hUe
  have hqbound : q≤a k.val := by
    have hc := balance_count b x
    have hl := matches_le b x
    simp only [Fintype.card_fin] at hc hl
    omega
  refine ⟨hodd,hdn,r,t,hr,hrn,htq,he,toOrdinary U,toOrdinary_uses (original G) U hUF,
    toOrdinary_ordinary U hUX,?_,hUnz,hvertices,hedge,?_⟩
  · rw [hdiag]
    exact hUb
  · rw [hvertices]
    have harity := (result G j ho hnz).arity_le
    omega

/- The residue is stated on every actual original row and supported word. -/
def OppositeDivisible (n : ℕ) (b : Bool) : Prop :=
  ∀ (k : Fin s) (x : Fin (a k.val) → Bool) (q : ℕ),
    sourceKBasis.symm.action (G k) x≠0 → 0<q → balance b x=q → n∣q

/-- A genuine original-input structural alternative.  Failure of the explicit
divisibility residue internally supplies the original witness and the smaller
odd graph; no proposed graph is passed to this declaration. -/
theorem source_or_divisibility (hh : 3≤(result G j ho hnz).arity) (b : Bool)
    (hy : endpoint G j ho hnz (!b)≠0) :
    (∃ d : ℕ, Odd d ∧ d<(result G j ho hnz).arity ∧
      ∃ U : Network AlgebraicComplex d, Uses U (original G) ∧ Ordinary U ∧
        U.denote≠0 ∧ U.shape.vertices≤a j.val+
          (Finset.univ.sup (fun k : Fin s => a k.val))-2) ∨
    OppositeDivisible G (result G j ho hnz).arity b := by
  classical
  by_cases h : OppositeDivisible G (result G j ho hnz).arity b
  · exact .inr h
  · simp only [OppositeDivisible] at h
    push Not at h
    obtain ⟨k,x,q,hx,hq,hcharge,hdiv⟩ := h
    obtain ⟨hd,hdn,r,t,hr,hrn,htq,he,U,hUF,hUE,hUb,hUnz,hUv,hUe,hbound⟩ :=
      source G j ho hnz hh b hy k x hx q hq hcharge hdiv
    refine .inl ⟨Nat.gcd q (result G j ho hnz).arity,hd,hdn,U,hUF,hUE,hUnz,?_⟩
    have hk : a k.val≤Finset.univ.sup (fun k : Fin s => a k.val) :=
      Finset.le_sup (f:=fun k : Fin s => a k.val) (Finset.mem_univ k)
    omega

/-- Select the supported terminal endpoint internally before classifying all
opposite original charges.  The divisibility branch remains an obligation for
the full odd dichotomy, and is not labelled tractable or hard. -/
theorem classified (hh : 3≤(result G j ho hnz).arity) :
    ∃ b : Bool,endpoint G j ho hnz (!b)≠0 ∧
      ((∃ d : ℕ, Odd d ∧ d<(result G j ho hnz).arity ∧
        ∃ U : Network AlgebraicComplex d, Uses U (original G) ∧ Ordinary U ∧
          U.denote≠0 ∧ U.shape.vertices≤a j.val+
            (Finset.univ.sup (fun k : Fin s => a k.val))-2) ∨
      OppositeDivisible G (result G j ho hnz).arity b) := by
  obtain ⟨b,hb⟩ := supported_endpoint G j ho hnz hh
  exact ⟨b,hb,source_or_divisibility G j ho hnz hh b hb⟩

end Original
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHighTerminalGcd
