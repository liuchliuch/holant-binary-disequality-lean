import Holant.Proofs.BinaryInterpolation.RawPolynomial
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.OriginalCounts
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Partition
import Holant.Complexity.BinaryInterpolation.AlgebraicSource.Pencil


namespace Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries
open Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation.Chains
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

variable {K : Type} [Field K]

theorem signature_linear {a n : ℕ} (f g : Signature K a) (u v : Signature K n)
    (hf : (⟨a, f⟩ : AnySignature K) = ⟨n, u⟩)
    (hg : (⟨a, g⟩ : AnySignature K) = ⟨n, v⟩) (q z : K) :
    (⟨a, q • (f + z • g)⟩ : AnySignature K) = ⟨n, q • (u + z • v)⟩ := by
  have h := congrArg Sigma.fst hf
  dsimp only at h
  subst n
  have hf' : f = u := eq_of_heq (Sigma.mk.inj_iff.mp hf).2
  have hg' : g = v := eq_of_heq (Sigma.mk.inj_iff.mp hg).2
  subst u
  subst v
  rfl

theorem templateSignature_eq {s b : ℕ} {ar : ℕ → ℕ}
    (g h : Template) (hg : g.WellFormed s b ar) (hh : h.WellFormed s b ar)
    (he : g = h) (S : (i : Fin s) → Signature K (ar i.val))
    (kernels : Fin b → Bool → Bool → K) :
    (⟨g.boundary, (g.network hg S kernels).denote⟩ : AnySignature K) =
      ⟨h.boundary, (h.network hh S kernels).denote⟩ := by
  cases he
  rfl

variable {s b : ℕ} (arity : ℕ → ℕ) (g : Template)
variable (hg : g.WellFormed s b arity) (hbinary : g.boundary = 2) (edge : Fin b)

abbrev A := Compiler.OriginalFamily.macroArity (s:=s) arity g
abbrev Source := FixedGadgetSubstitution.Compiler.Input (s+1) b (A (s:=s) arity g)
abbrev Sample := Compiler.OriginalFamily.Input (s:=s) (b:=b) arity g
abbrev newLabel : Fin (s+1) := ⟨s, Nat.lt_succ_self s⟩

include hbinary in
theorem new_arity : A (s:=s) arity g s = 2 :=
  (Adjoin.new_boundary g).trans hbinary

include hbinary in
theorem chain_arity (k : ℕ) :
    sourceArity (Compiler.Occurrence.templates (A (s:=s) arity g) s s edge.val k) =
      A (s:=s) arity g := by
  funext i
  by_cases hi : i = s
  · subst i
    simpa [sourceArity, Compiler.Occurrence.templates, explicitTemplate] using
      (new_arity (s:=s) arity g hbinary).symm
  · simp [sourceArity, Compiler.Occurrence.templates, hi, identityTemplate]

variable (S L R : (i : Fin (s+1)) → Signature K (A (s:=s) arity g i.val))
variable (G : (i : Fin s) → Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)
variable (B C H : Binary (K:=K)) (beta : K) (node : ℕ → K)
variable (hB : (⟨A (s:=s) arity g s, S newLabel⟩ : AnySignature K) =
  ⟨2, binarySignature B⟩)
variable (hL : (⟨A (s:=s) arity g s, L newLabel⟩ : AnySignature K) =
  ⟨2, binarySignature C⟩)
variable (hR : (⟨A (s:=s) arity g s, R newLabel⟩ : AnySignature K) =
  ⟨2, binarySignature H⟩)
variable (hX : kernels edge = Signature.disequality)
variable (hpower : ∀ t : ℕ, (B * X)^t * X = beta^t • (C + node t • H))

include hB hL hR hX hpower in
/-- Derived local identities for all labels: old vertices are literal
corollas and each marked occurrence is a positive physical B-chain. -/
theorem chain_local (k : ℕ) (i : Fin (s+1)) :
    (⟨(Compiler.Occurrence.templates (A (s:=s) arity g) s s edge.val k i.val).boundary,
      ((Compiler.Occurrence.templates (A (s:=s) arity g) s s edge.val k i.val).network
        (Compiler.OriginalFamily.chain_hypotheses arity g hbinary edge k i.val i.isLt).1
        S kernels).denote⟩ : AnySignature K) =
    ⟨A (s:=s) arity g i.val,
      (if i.val = s then beta^(k+1) else 1) •
        RawPolynomial.pencil S L R s (node (k+1)) i⟩ := by
  by_cases hi : i.val = s
  · have hi' : i = newLabel := Fin.ext hi
    subst i
    have ht : Compiler.Occurrence.templates (A (s:=s) arity g) s s edge.val k s =
        explicitTemplate s edge.val k := by simp [Compiler.Occurrence.templates]
    have hs := templateSignature_eq _ _
        (Compiler.OriginalFamily.chain_hypotheses arity g hbinary edge k s (Nat.lt_succ_self s)).1
        (explicitTemplate_wellFormed (A (s:=s) arity g) newLabel
          (new_arity (s:=s) arity g hbinary) edge k) ht S kernels
    rw [hs]
    rw [explicitTemplate_denote (A (s:=s) arity g) newLabel
      (new_arity (s:=s) arity g hbinary) edge k B S kernels hB hX, hpower]
    have h := signature_linear (L newLabel) (R newLabel)
      (binarySignature C) (binarySignature H) hL hR (beta^(k+1)) (node (k+1))
    have hm : binarySignature (beta^(k+1) • (C + node (k+1) • H)) =
        beta^(k+1) • (binarySignature C + node (k+1) • binarySignature H) := rfl
    rw [hm]
    change (⟨2, beta^(k+1) • (binarySignature C + node (k+1) • binarySignature H)⟩ : AnySignature K) = _
    trans (⟨A (s:=s) arity g s, beta^(k+1) • (L newLabel + node (k+1) • R newLabel)⟩ : AnySignature K)
    · exact h.symm
    · congr 1
      funext x
      simp [RawPolynomial.pencil, newLabel]
  · have ht : Compiler.Occurrence.templates (A (s:=s) arity g) s s edge.val k i.val =
        identityTemplate (A (s:=s) arity g) i.val := by simp [Compiler.Occurrence.templates, hi]
    have hs := templateSignature_eq _ _
        (Compiler.OriginalFamily.chain_hypotheses arity g hbinary edge k i.val i.isLt).1
        (identityTemplate_wellFormed (A (s:=s) arity g) i) ht S kernels
    rw [hs]
    rw [identityTemplate_denote (A (s:=s) arity g) i S kernels]
    congr 1
    funext x
    simp [RawPolynomial.pencil, hi]

include hB hL hR hX hpower in
/-- The actual intermediate byte compiler's value is now proved from the
local path records. This supplies the formerly external spectral equation. -/
theorem intermediate_partition (x : Sample (s:=s) (b:=b) arity g) :
    ((Compiler.OriginalFamily.intermediate arity g hbinary edge x).val.realize
      (Compiler.OriginalFamily.intermediate arity g hbinary edge x).property S kernels).denote
      Fin.elim0 =
    beta^((x.2.val+1) * occurrences s x.1.val) *
      (RawPolynomial.polynomial x.1.val x.1.property S L R kernels s).eval (node (x.2.val+1)) := by
  let ts := Compiler.Occurrence.templates (A (s:=s) arity g) s s edge.val x.2.val
  obtain ⟨hq, hqval⟩ := RawPolynomial.replacement_same_arity x.1.val x.1.property
    (RawPolynomial.pencil S L R s (node (x.2.val+1))) kernels s ts
    (fun i hi => (Compiler.OriginalFamily.chain_hypotheses arity g hbinary edge x.2.val i hi).1)
    (chain_arity arity g hbinary edge x.2.val) S (beta^(x.2.val+1))
    (chain_local arity g hbinary edge S L R kernels B C H beta node hB hL hR hX hpower x.2.val)
  have he : (Compiler.OriginalFamily.intermediate arity g hbinary edge x).val =
      replace ts x.1.val :=
    Compiler.Occurrence.raw_eq_replace (s+1) b (A (s:=s) arity g) s s edge.val (x.2.val,x.1)
  have hd := Compiler.Validated.raw_denote_congr _ _
    (Compiler.OriginalFamily.intermediate arity g hbinary edge x).property hq he S kernels
  rw [hqval, ← pow_mul, ← RawPolynomial.polynomial_eval] at hd
  exact hd

variable (c : K)
variable (hmacro : ∀ i : Fin (s+1),
  ((Adjoin.templates s arity g i.val).network (Adjoin.wellFormed g hg i.val i.isLt)
    G kernels).denote = (if i.val = s then c else 1) • S i)

include hB hL hR hX hpower hmacro in
/-- Literal original-Γ query value, including both the macro and spectral
scale once for each of the t*m actual B occurrences. -/
theorem query_partition (x : Sample (s:=s) (b:=b) arity g) :
    ((Compiler.OriginalFamily.value arity g hg hbinary edge x).val.realize
      (Compiler.OriginalFamily.value arity g hg hbinary edge x).property G kernels).denote
      Fin.elim0 =
    (c*beta)^((x.2.val+1)*occurrences s x.1.val) *
      (RawPolynomial.polynomial x.1.val x.1.property S L R kernels s).eval (node (x.2.val+1)) := by
  apply Compiler.OriginalFamily.value_partition_normalized arity g hg hbinary edge x
    S G kernels c beta _ hmacro
  exact intermediate_partition arity g hbinary edge S L R kernels
    B C H beta node hB hL hR hX hpower x

include hB hL hR hX hpower hmacro in
/-- The values returned by exactly the actual Γ queries recover the all-H
network; no assumption about an already-existing reduction occurs here. -/
theorem recovery (r : Source (s:=s) (b:=b) arity g)
    (hc : c ≠ 0) (hbeta : beta ≠ 0)
    (hnodes : Function.Injective
      (fun i : Fin (occurrences s r.val+1) => node (i.val+1))) :
    recoverTop (fun i : Fin (occurrences s r.val+1) => node (i.val+1))
      (fun i =>
        ((Compiler.OriginalFamily.value arity g hg hbinary edge ⟨r,i⟩).val.realize
          (Compiler.OriginalFamily.value arity g hg hbinary edge ⟨r,i⟩).property G kernels).denote
            Fin.elim0 / (c*beta)^((i.val+1)*occurrences s r.val)) =
      (r.val.realize r.property (RawPolynomial.right S R s) kernels).denote Fin.elim0 := by
  have he : (fun i : Fin (occurrences s r.val+1) =>
      ((Compiler.OriginalFamily.value arity g hg hbinary edge ⟨r,i⟩).val.realize
        (Compiler.OriginalFamily.value arity g hg hbinary edge ⟨r,i⟩).property G kernels).denote
          Fin.elim0 / (c*beta)^((i.val+1)*occurrences s r.val)) =
      (fun i => (RawPolynomial.polynomial r.val r.property S L R kernels s).eval (node (i.val+1))) := by
    funext i
    rw [query_partition arity g hg hbinary edge S L R G kernels
      B C H beta node hB hL hR hX hpower c hmacro]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (mul_ne_zero hc hbeta))
  rw [he, recoverTop_eq_coefficient _ hnodes _
    (RawPolynomial.polynomial_degree r.val r.property S L R kernels s), RawPolynomial.polynomial_top]

end
end Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries
