
n := 4; // messages length.  // from 21 and on, Zech log tables are used ; for lesser n values, the exponents go up without any limitation.
D := 5; // degree of the F polynom.
m := n-1; // number of equations in the f polynomial system.
v := 2; // number of vinegar variables.

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

UPF2n<X> := PolynomialRing(F2n);  // univariate

PF2n := PolynomialRing(F2n, v+1); // multivariate with vinegars
vars := ["X"] cat ["v" cat IntegerToString(i) : i in [1..v]];
AssignNames(~PF2n, vars);

MPF2n := PolynomialRing(F2n,n+v);
xi := ["x" cat IntegerToString(i) : i in [1..n]] cat ["v" cat IntegerToString(i) : i in [1..v]];
AssignNames(~MPF2n, xi);

F2n_to_PF2 := hom < F2n -> PF2 | b >;
MPF2n_to_PF2n := hom < MPF2n -> PF2n | [1 : i in [1..n]] cat [PF2n.i : i in [2..v+1]] >;
PF2n_to_UPF2n := hom < PF2n -> UPF2n | [X] cat [1 : i in [1..v]] >;
F2n_to_UPF2n := hom < F2n -> UPF2n | a >;
// MPF2n_to_UPF2n := hom < MPF2n -> UPF2n | [1 : i in [1..n+v]] >;

X_exp_2_exp_i := function(n, i)
  return (&+ [MPF2n.k*a^((k-1)*2^i) : k in [1..n]]);
end function;

make_A := function(D,n)
  A := Matrix(F2n,n,n,[0 : i,j in [1..n]]);  // upper triangular matrix
  for j in [2..n] do
    for i in [1..(j-1)] do
      if 2^(i-1)+2^(j-1) le D then
        A[i,j] := Random(F2n);
      end if;
    end for;
  end for;
  return A;
end function;

make_F := function(D,n,v)
  A := make_A(D,n);  // upper triangular matrix
  B := Matrix(n,v,[Random(F2n) : i in [1..n*v]]);
  C := &+ [Random(F2n)*MPF2n.i : i in [n+1..n+v]];
  try
    C +:= &+ [ &+ [Random(F2n)*MPF2n.i*MPF2n.j : j in [n+1..(i-1)]] : i in [n+2..(n+v)]] ;
  catch e
    "There is only one vinegar variable"; // we have an error if v eq 1 because then the sum quadratic sequence is null.
  end try;
  multivariateF := &+ [ &+ [ A[i+1,j+1]*X_exp_2_exp_i(n,i)*X_exp_2_exp_i(n,j) : i in [0..j] ] : j in [0..(n-1)] ] + &+ [ (&+ [B[i+1,(k-n)]*MPF2n.k : k in [n+1..n+v]])*X_exp_2_exp_i(n,i) : i in [0..n-1]] + C;
  univariateF := &+ [ &+ [ A[i+1,j+1]*PF2n.1^(2^i+2^j) : i in [0..j] ] : j in [0..(n-1)] ] + &+ [(&+ [B[i+1,k-1]*PF2n.k : k in [2..v+1]])*PF2n.1^(2^i) : i in [0..n-1]] + MPF2n_to_PF2n(C);
  return multivariateF, univariateF;
end function;

F, univF := make_F(D,n,v);
print "F(X) = ", univF;

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
    b_Polynom := F2n_to_PF2(Coeffs[c]); // this will write the polynom of a coeff
                  // as a sum of a with exponents inferior to n, and will also allow us
                  // to get a list of coefficients (this is not possible in  F2n).
    b_Coeffs := Coefficients(b_Polynom);
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


S := RandomMatrix(F2,n+v,n+v);
T := RandomMatrix(F2,n,n);
while Determinant(S) eq 0 do
  S := RandomMatrix(F2,n+v,n+v);
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

x := Matrix(n+v,1,[MPF2n.i : i in [1..n+v]]);
Sx := S*x;

get_pol_sys_fiSx := function(pol_sys_fi, Sx, n)
  pol_sys_fiSx := Matrix(MPF2n, n, 1, [0 : i in [1..n]]);
  for i in [1..n] do
    Monoms := Monomials(pol_sys_fi[i]);
    for mon in Monoms do
      Exps := Exponents(mon);
      if Exps eq [0 : k in [1..n]] then
        pol_sys_fiSx[i,1] := pol_sys_fiSx[i,1] + mon;
      else
        add := &*[Sx[k][1]^Exps[k] : k in [1..n]];
        simplified_add := 0;
        for M in Monomials(add) do
          if 2 in Exponents(M) then
            simplified_add := simplified_add + Sqrt(M);
          else
            simplified_add := simplified_add + M;
          end if;
        end for;
        pol_sys_fiSx[i,1] := pol_sys_fiSx[i,1] + simplified_add;
      end if;
    end for;
  end for;
  return pol_sys_fiSx;
end function;

pol_sys_fiSx := get_pol_sys_fiSx(pol_sys_fi, Sx, n);

public_key := Matrix(m,1,[(T*pol_sys_fiSx)[i,1] : i in [1..m]]);
print("Clé publique : ");
public_key;
