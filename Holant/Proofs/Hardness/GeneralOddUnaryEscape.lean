import Holant.Proofs.Reductions.GeneralExtraction.SupportCaps
import Holant.Proofs.Reductions.GeneralExtraction.NativeCopies

/-!
# A supplied isotropic unary escapes its line from actual opposing support

This is a local producer for the unary arm of the ordinary odd descent, in
the diagnostic K chart.  Its input is an actual unary graph and an actual
supported word of opposite strict charge in an original row.  It constructs
a unary graph with nonzero opposite entry.  No desired unary, hard basis,
separation, or terminating search is an input.  All original vertices and
their scalar weights are retained.  The high-odd arm and the remaining
whole-family hardness classification are deliberately not asserted here.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnaryEscape
open Holant
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps NativeCopies
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {k n : ℕ}

/-- Attach the actual unary graph to the first remaining port, by one X edge.
The surviving boundary is the tail of the original boundary in its old order. -/
def capHead (U : Network K 1) (N : Network K (k+1)) : Network K k :=
  (reboundary (U.tensor N) (finCongr (by omega : 1+(k+1)=k+2))).contract
    Signature.disequality

private theorem cap_left (a b : Bool) (x : Fin k → Bool) :
    (fun i : Fin 1 => (Fin.cons a (Fin.cons b x) : Fin (k+2) → Bool)
      ((finCongr (by omega : 1+(k+1)=k+2)) (Fin.castAdd (k+1) i)))=
      (fun _ => a) := by
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rfl

private theorem cap_right (a b : Bool) (x : Fin k → Bool) :
    (fun i : Fin (k+1) => (Fin.cons a (Fin.cons b x) : Fin (k+2) → Bool)
      ((finCongr (by omega : 1+(k+1)=k+2)) (Fin.natAdd 1 i)))=Fin.cons b x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have he : (finCongr (by omega : 1+(k+1)=k+2)) (Fin.natAdd 1 j.succ)=j.succ.succ := by
      apply Fin.ext
      simp
    rw [he]
    rfl

theorem capHead_denote (U : Network K 1) (N : Network K (k+1))
    (x : Fin k → Bool) :
    (capHead U N).denote x=
      U.denote (fun _ => false)*N.denote (Fin.cons true x)+
      U.denote (fun _ => true)*N.denote (Fin.cons false x) := by
  rw [capHead,Network.denote_contract]
  simp only [Signature.contract,reboundary_denote,Network.denote_tensor,
    Signature.tensor_apply,cap_left,cap_right]
  simp [Signature.disequality,add_comm]

theorem capHead_pin (U : Network K 1) (N : Network K (k+1))
    (c : K) (b : Bool) (hU : U.denote=purePin c (!b) 1)
    (x : Fin k → Bool) :
    (capHead U N).denote x=c*N.denote (Fin.cons b x) := by
  rw [capHead_denote,hU]
  cases b <;> simp [purePin,funext_iff]

theorem capHead_uses (F : SignatureFamily K) (U : Network K 1)
    (N : Network K (k+1)) (hU : Uses U F) (hN : Uses N F) :
    Uses (capHead U N) F := tensor_uses F U N hU hN

theorem capHead_native (U : Network K 1) (N : Network K (k+1))
    (hU : Native U) (hN : Native N) : Native (capHead U N) := by
  intro e
  refine Fin.cases rfl (fun e => ?_) e
  exact tensor_native U N hU hN e

theorem capHead_vertices (U : Network K 1) (N : Network K (k+1)) :
    (capHead U N).shape.vertices=U.shape.vertices+N.shape.vertices :=
  Network.tensor_vertices U N

theorem capHead_edges (U : Network K 1) (N : Network K (k+1)) :
    (capHead U N).shape.edges=1+U.shape.edges+N.shape.edges := by
  change (U.tensor N).shape.edges+1=_
  rw [Network.tensor_edges]
  omega

/-- Cap every port except the final one, using fresh copies of the same actual
unary graph.  The definition decreases the number of original boundary ports. -/
def capToUnary (U : Network K 1) : (k : ℕ) → Network K (k+1) → Network K 1
  | 0,N => N
  | k+1,N => capToUnary U k (capHead U N)

/-- The first k OLD boundary ports are pinned and the final port survives. -/
def capWord (b t : Bool) : (k : ℕ) → Fin (k+1) → Bool
  | 0 => fun _ => t
  | k+1 => Fin.cons b (capWord b t k)

theorem capWord_last (b t : Bool) (k : ℕ) : capWord b t k (Fin.last k)=t := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem capWord_pinned (b t : Bool) (k : ℕ) (i : Fin k) :
    capWord b t k i.castSucc=b := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact ih j

/-- Pointwise equality keeps the full scalar c^k, including the other surviving
entry. No normalized synthetic signature replaces a real unary occurrence. -/
theorem capToUnary_entry (U : Network K 1) (c : K) (b : Bool)
    (hU : U.denote=purePin c (!b) 1) (k : ℕ) (N : Network K (k+1)) (t : Bool) :
    (capToUnary U k N).denote (fun _ => t)=c^k*N.denote (capWord b t k) := by
  induction k with
  | zero => simp [capToUnary,capWord]
  | succ k ih =>
    rw [capToUnary,ih,capHead_pin U N c b hU]
    simp only [capWord,pow_succ]
    ring

theorem capToUnary_constant (U : Network K 1) (c : K) (b : Bool)
    (hU : U.denote=purePin c (!b) 1) (k : ℕ) (N : Network K (k+1)) :
    (capToUnary U k N).denote (fun _ => b)=c^k*N.denote (fun _ => b) := by
  induction k with
  | zero => simp [capToUnary]
  | succ k ih =>
    rw [capToUnary,ih,capHead_pin U N c b hU]
    have he : Fin.cons b (fun _ : Fin (k+1) => b)=(fun _ => b) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [he,pow_succ]
    ring

theorem capToUnary_uses (F : SignatureFamily K) (U : Network K 1)
    (hU : Uses U F) (k : ℕ) (N : Network K (k+1)) (hN : Uses N F) :
    Uses (capToUnary U k N) F := by
  induction k with
  | zero => exact hN
  | succ k ih => exact ih _ (capHead_uses F U N hU hN)

theorem capToUnary_native (U : Network K 1) (hU : Native U)
    (k : ℕ) (N : Network K (k+1)) (hN : Native N) :
    Native (capToUnary U k N) := by
  induction k with
  | zero => exact hN
  | succ k ih => exact ih _ (capHead_native U N hU hN)

theorem capToUnary_vertices (U : Network K 1) (k : ℕ) (N : Network K (k+1)) :
    (capToUnary U k N).shape.vertices=k*U.shape.vertices+N.shape.vertices := by
  induction k with
  | zero => simp [capToUnary]
  | succ k ih =>
    rw [capToUnary,ih,capHead_vertices]
    ring

theorem capToUnary_edges (U : Network K 1) (k : ℕ) (N : Network K (k+1)) :
    (capToUnary U k N).shape.edges=k*(U.shape.edges+1)+N.shape.edges := by
  induction k with
  | zero => simp [capToUnary]
  | succ k ih =>
    rw [capToUnary,ih,capHead_edges]
    ring

/-- A positive-charge support coefficient yields an independent unary from a
pure opposite pin.  The noncancellation support descent is run internally;
its resulting arity is the original word's exact charge. -/
theorem escape (F : SignatureFamily K) (htwo : (2 : K)≠0)
    (U : Network K 1) (hUF : Uses U F) (hUX : Native U)
    (c : K) (hc : c≠0) (b : Bool) (hU : U.denote=purePin c (!b) 1)
    (f : Signature K n) (hf : (⟨n,f⟩ : AnySignature K)∈F)
    (x : Fin n → Bool) (hx : f x≠0) (hpos : 0<balance b x) :
    ∃ k : ℕ, k+1≤n ∧ ((k+1 : ℕ) : ℤ)=balance b x ∧
      ∃ V : Network K 1, Uses V F ∧ Native V ∧ V.denote (fun _ => b)≠0 ∧
        V.shape.vertices=k*U.shape.vertices+1 := by
  obtain ⟨m,hm,M,hMF,hMX,hMv,hcharge,hMb⟩ := support_cap htwo b f x hx hpos
  obtain ⟨k,rfl⟩ : ∃k,m=k+1 := ⟨m-1,by omega⟩
  have hkn : k+1≤n := by
    have hcount := balance_count b x
    have hle := matches_le b x
    simp only [Fintype.card_fin] at hcount hle
    omega
  have hMF' : Uses M F := by
    intro v
    rw [Set.mem_singleton_iff.mp (hMF v)]
    exact hf
  refine ⟨k,hkn,hcharge,capToUnary U k M,capToUnary_uses F U hUF k M hMF',
    capToUnary_native U hUX k M hMX,?_,?_⟩
  · rw [capToUnary_constant U c b hU]
    exact mul_ne_zero (pow_ne_zero k hc) hMb
  · rw [capToUnary_vertices,hMv]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnaryEscape
