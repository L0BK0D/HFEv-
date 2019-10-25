
n := 15; // messages length.  // from 21 and on, Zech log tables are used ; for lesser n values, the exponents go up without any limitation.
D := 5; // degree of the F polynom.

/////////////////////////////////
// Génération de la clé secrète :
/////////////////////////////////

// depliage de corps de F_2^n dans F_2

F2 := GF(2:Optimize:=true); // F2
PF2<b> := PolynomialRing(F2); // only to have "I" written with the b variable. No necessary use.
I := IrreduciblePolynomial(F2,n);
print("Polynôme irréductible : ");
I;
F2n<a> := ext<F2|I>; // extension de F2 à F2^n par le polynôme irréductible b^n+b+1

PF2n<X> := PolynomialRing(F2n);
// F := a^3*X^3 + a^4*X^2 + a*X + a^2;

MPF2n := PolynomialRing(F2n,n);
xi := ["x" cat IntegerToString(i) : i in [1..n]];
AssignNames(~MPF2n, xi);

// X := &+ [MPF2n.i*a^(i-1) : i in [1..n]] ;  // we won use X, because we have the function below;
X_exp_2_exp_i := function(n, i)
    return (&+ [MPF2n.k*a^((k-1)*2^i) : k in [1..n]]);
end function;
// X_exp_2_exp_i(n,3);
// chgmnt_var := hom < MPF2n -> PF2n | Somme >;

make_A := function(D,n)
  A := Matrix(F2n,n,n,[0 : i,j in [1..n]]);  // upper triangular matrix
  for j in [1..n] do
    for i in [1..j] do
      if 2^(i-1)+2^(j-1) le D then
        A[i,j] := Random(F2n);
      end if;
    end for;
  end for;
  return A;
end function;

make_F := function(D,n)
  A := make_A(D,n);  // upper triangular matrix
  B := Random(F2n);
  C := Random(F2n);
  multivariateF := &+ [ &+ [ A[i+1,j+1]*X_exp_2_exp_i(n,i)*X_exp_2_exp_i(n,j) : i in [0..j] ] : j in [0..(n-1)] ] + B*(&+ [MPF2n.k*a^(k-1) : k in [1..n]]) + C;
  univariateF := &+ [ &+ [ A[i+1,j+1]*X^(2^i+2^j) : i in [0..j] ] : j in [0..(n-1)] ] + B*X + C;
  return multivariateF, univariateF;
end function;

// F:= a^3*X^3 + a^4*X^2 + a*X + a^2;
F, univF := make_F(D,n);
print "F(X) = ", univF;
// F;

F2n_to_PF2 := hom < F2n -> PF2 | b >;
// coeff := F2n_to_PF2(Coefficients(F)[1]);
// coeff;
// Coefficients(coeff);

// Draft for changing F entirely, gave it up; anyways it wasn't necessary at all.
// MPF2 := PolynomialRing(PF2,n);
// AssignNames(~MPF2, xi);
// MPF2n_to_MPF2 := hom < MPF2n -> MPF2 | [MPF2.i : i in [1..n]] >;
// Fbis := MPF2n_to_MPF2(F);
// Fbis;

get_pol_sys_fi := function(F,n)  // we will use the canonical basis
  pol_sys_fi := [ 0 : i in [0..(n-1)]];
  pol_sys_fi := ChangeUniverse(pol_sys_fi, MPF2n); // default universe is the universe of integers.
  Coeffs := Coefficients(F);
  Monoms := Monomials(F);
  Nb_F_coeffs := #Coeffs;
  for c in [1..Nb_F_coeffs] do
    b_polynom := F2n_to_PF2(Coeffs[c]); // this will write the polynom of a coeff
                  // as a sum of a with exponents inferior to n, and will also allow us
                  // to get a list of coefficients (this is not possible in  F2n).
    b_Coeffs := Coefficients(b_polynom);
    mon := Monoms[c];
    for i in [1..n] do
      if Monoms[c] eq MPF2n.i*MPF2n.i then
        mon := MPF2n.i;
      end if;
    end for;
    for k in [1..#b_Coeffs] do
      if b_Coeffs[k] eq 1 then
        pol_sys_fi[k] := pol_sys_fi[k] + mon;
      end if;
    end for;
  end for;
  return pol_sys_fi;
end function;

pol_sys_fi := get_pol_sys_fi(F,n);
print("Système polynomial f : ");
pol_sys_fi;


S := RandomMatrix(F2,n,n);
T := RandomMatrix(F2,n,n);
while Determinant(S) eq 0 do
  S := RandomMatrix(F2,n,n);
end while;
while Determinant(T) eq 0 do
  T := RandomMatrix(F2,n,n);
end while;
S := ChangeRing(S, MPF2n); // to allow multiplication with elements in MPF2n
T := ChangeRing(T, MPF2n);
print("Matrice de changement de variables S : ");
S;
print("Matrice de mélange d'équations T : ");
T;


//////////////////////////////////
// Génération de la clé publique :
//////////////////////////////////

x := Matrix(n,1,[MPF2n.i : i in [1..n]]);
Sx := S*x;

get_pol_sys_fiSx := function(pol_sys_fi, Sx,n)
  pol_sys_fiSx := Matrix(MPF2n, n,1,[0 : i in [1..n]]);
  for i in [1..n] do
    Monoms := Monomials(pol_sys_fi[i]);
    for mon in Monoms do
      Exps := Exponents(mon);
      if Exps eq [0 : k in [1..n]] then
        pol_sys_fiSx[i,1] := pol_sys_fiSx[i,1] + mon;
      else
        add := &*[Sx[k][1]^Exps[k] : k in [1..n]];
        simplified_add := 0;
        for m in Monomials(add) do
          if 2 in Exponents(m) then
            simplified_add := simplified_add + Sqrt(m);
          else
            simplified_add := simplified_add + m;
          end if;
        end for;
        pol_sys_fiSx[i,1] := pol_sys_fiSx[i,1] + simplified_add;
      end if;
    end for;
  end for;
  return pol_sys_fiSx;
end function;

pol_sys_fiSx := get_pol_sys_fiSx(pol_sys_fi, Sx, n);

public_key := T*pol_sys_fiSx;
print("Clé publique : ");
public_key;
