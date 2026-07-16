import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder

/-!
# The Pasta GLV endomorphism anchors

Each Pasta curve `y² = x³ + 5` carries the GLV endomorphism `φ(x, y) = (β·x, y)` (`β` a
primitive cube root of unity in the base field), which acts on the point group as
multiplication by a scalar eigenvalue `λ`. This file provides the *computational anchor*
of that fact, one certificate per curve: `λ • G = φ(G)` at the standard generator,
checked by `native_decide` through the binary double-and-add `nsmul` — the same
certificate style as the point counts in `PastaOrder.lean`.

Downstream (the `pasta` package of l-adic/snarky) the anchor extends to every point:
`φ` is a group homomorphism (field algebra over `β³ = 1`), the group is cyclic of prime
order (Hasse), so `φ(kG) = k·φ(G) = k·λ·G = λ·(kG)`.
-/

namespace CompElliptic.Curves.Pasta

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Fields.Pasta

namespace Pallas

/-- The Pallas base-field endomorphism coefficient `β` (a primitive cube root of unity). -/
def endoBeta : Fp :=
  20444556541222657078399132219657928148671392403212669005631716460534733845831

/-- The scalar eigenvalue `λ` of the Pallas endomorphism, as a natural number. -/
def endoLam : ℕ :=
  26005156700822196841419187675678338661165322343552424574062261873906994770353

/-- The image of the standard generator under `φ(x, y) = (β·x, y)`. -/
def endoGpt : SWPoint curve :=
  ⟨endoBeta * G.1, G.2, by
    left
    show G.2 ^ 2 = (endoBeta * G.1) ^ 3 + a * (endoBeta * G.1) + b
    decide⟩

/-- **The eigenvalue anchor**: `λ • G = φ(G)` at the standard generator. -/
theorem endoLam_nsmul_Gpt : endoLam • Gpt = endoGpt := by native_decide

end Pallas

namespace Vesta

/-- The Vesta base-field endomorphism coefficient `β` (a primitive cube root of unity). -/
def endoBeta : Fq :=
  2942865608506852014473558576493638302197734138389222805617480874486368177743

/-- The scalar eigenvalue `λ` of the Vesta endomorphism, as a natural number. -/
def endoLam : ℕ :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

/-- The image of the standard generator under `φ(x, y) = (β·x, y)`. -/
def endoGpt : SWPoint curve :=
  ⟨endoBeta * G.1, G.2, by
    left
    show G.2 ^ 2 = (endoBeta * G.1) ^ 3 + a * (endoBeta * G.1) + b
    decide⟩

/-- **The eigenvalue anchor**: `λ • G = φ(G)` at the standard generator. -/
theorem endoLam_nsmul_Gpt : endoLam • Gpt = endoGpt := by native_decide

end Vesta

end CompElliptic.Curves.Pasta
