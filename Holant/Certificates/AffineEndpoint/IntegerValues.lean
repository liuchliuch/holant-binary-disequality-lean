import Holant.Certificates.AffineEndpoint.Scalars
import Holant.Certificates.OctahedralSeparator.IntegerChecker

/-! Faithful integer-coordinate arithmetic for the endpoint certificates. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Certificates.OctahedralSeparator
namespace IntegerValues
abbrev Coeff := IntegerCoefficient

def zero : Coeff := ⟨0,0,0,0⟩
def one : Coeff := ⟨1,0,0,0⟩
def rotate (z : Coeff) (e : Fin 4) : Coeff :=
  ![z,⟨-z.c,-z.d,z.a,z.b⟩,⟨-z.a,-z.b,-z.c,-z.d⟩,⟨z.c,z.d,-z.a,-z.b⟩] e

def sum : List Coeff → Coeff
  | [] => zero
  | z::zs => IntegerCoefficient.add z (sum zs)

 theorem eval_zero : IntegerCoefficient.eval zero=0 := rfl
 theorem eval_one : IntegerCoefficient.eval one=1 := rfl
 theorem eval_injective : Function.Injective IntegerCoefficient.eval := by
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  have ha := congrArg (fun z : Scalar => z.re.re) h
  have hb := congrArg (fun z : Scalar => z.im.re) h
  have hc := congrArg (fun z : Scalar => z.re.im) h
  have hd := congrArg (fun z : Scalar => z.im.im) h
  simp only [IntegerCoefficient.eval,coeff] at ha hb hc hd
  have ha' : a=a' := Int.cast_injective ha
  have hb' : b=b' := Int.cast_injective hb
  have hc' : c=c' := Int.cast_injective hc
  have hd' : d=d' := Int.cast_injective hd
  subst a'; subst b'; subst c'; subst d'; rfl

 theorem eval_ne_zero {z : Coeff} (hz : z≠zero) : IntegerCoefficient.eval z≠0 :=
  fun h => hz (eval_injective (h.trans eval_zero.symm))

 theorem eval_rotate (z : Coeff) (e : Fin 4) :
    IntegerCoefficient.eval (rotate z e)=IntegerCoefficient.eval z*imag^e.val := by
  have hi : embed imag=Complex.I := by simp [imag,embed_coeff]
  have hp (n : ℕ) : embed (imag^n)=(embed imag)^n := map_pow embedding _ _
  fin_cases e <;> apply embed_injective <;>
    simp [rotate,IntegerCoefficient.eval,embed_mul,hp,hi,embed_coeff,Complex.I_sq,Complex.I_pow_three] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring

 theorem eval_sum (zs : List Coeff) :
    IntegerCoefficient.eval (sum zs)=(zs.map IntegerCoefficient.eval).sum := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [sum,IntegerCoefficient.eval_add,ih]

 noncomputable def alg (z : Coeff) : AlgebraicComplex := algebraicEmbed (IntegerCoefficient.eval z)
 theorem alg_zero : alg zero=0 := algebraicEmbed_zero
 theorem alg_one : alg one=1 := algebraicEmbed_one
 theorem alg_injective : Function.Injective alg := algebraicEmbed_injective.comp eval_injective
 theorem alg_ne_zero {z : Coeff} (hz : z≠zero) : alg z≠0 :=
  algebraicEmbed_ne_zero (eval_ne_zero hz)
 theorem alg_add (z w : Coeff) : alg (IntegerCoefficient.add z w)=alg z+alg w := by
  simp [alg,IntegerCoefficient.eval_add]
 theorem alg_mul (z w : Coeff) : alg (IntegerCoefficient.mul z w)=alg z*alg w := by
  simp [alg,IntegerCoefficient.eval_mul]

end IntegerValues
end Holant.Certificates.AffineEndpoint
