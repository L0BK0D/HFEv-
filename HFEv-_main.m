load "HFEv-_generate_keys.m";

invert_phi := function(vector,l)
  if Type(vector) eq SeqEnum then
    sum := &+ [vector[k]*a^(k-1) : k in [1..#vector]];
    if l gt #vector then
      sum +:= &+ [Random(F2)*a^(k-1) : k in [1..(l-#vector)]];
    end if;
    return sum;
  else
    sum := 0;
    for k in [1..l] do
      try
        sum +:= vector[k][1]*a^(k-1);
      catch e
        sum +:= Random(F2)*a^(k-1);
      end try;
    end for;
    return sum;
  end if;
end function;

phi := function(Z,l) // Z is in MPF2n
  canon := F2n_to_PF2(Z);  //p expressed as a polynom with b coefficients in the canonical base.
  vect_Z := Matrix(F2,l,1,[0 : k in [1..l]]);
  for i in [1..#Coefficients(canon)] do
    vect_Z[i][1] := Coefficients(canon)[i];
  end for;
  return vect_Z;
end function;

cipher := function(message, public_key, vinegars, m)
  not_pol_ring := Evaluate(public_key, message cat vinegars);
  return Matrix(F2,m,1,[not_pol_ring[k] : k in [1..m]]);
end function;

apply_F := function(message,univF) // you still need to reduce the dimension after that.
  MPF2n_message := invert_phi(message, n); // = &+ [message[k]*a^(k-1) : k in [1..n]];
  return Evaluate(univF,MPF2n_message);
end function;

invert := function(d, univF, S, T, n, m, v)
  // T^(-1)*d; // incompatible coefficient rings
  roots := [];
  invT := T^(-1);
  while #roots eq 0 do
    completion := Matrix(n-m, 1, [Random(F2) : i in [1..n-m]]);
    MPF2n_invT_d := invert_phi(Matrix(F2,n,1,[&+[d[i]*invT[k,i] : i in [1..m]] + &+[completion[i]*invT[k,i+m] : i in [1..n-m]] : k in [1..n]]), n);
    vinegar := [Random(F2) : k in [1..v]]; // TODO: change from Random to ordered logic
    F_with_these_Vs := PF2n_to_UPF2n(Evaluate(univF, [PF2n.1] cat [vinegar[k] : k in [1..v]]));
    try
      roots := Roots(F_with_these_Vs-MPF2n_invT_d);
    catch e
      print e;  // if F_with_these_Vs-MPF2n_invT_d is null, an error will be displayed.
    end try;
  end while;
  r := Random(roots);  // maybe we should give more weight to roots with higher multiplicity? -> TODO
  vect_r := Matrix(n+v, 1, [phi(r[1],n)[k][1]:k in [1..n]] cat vinegar);  // vertical matrix in F2;  // TODO: include vinegars here.
  invS := S^(-1);
  return Matrix(F2,n+v,1,[&+[vect_r[i][1]*invS[k,i] : i in [1..n+v]] : k in [1..n+v]]), vinegar;
end function;

sign := function(message, univF, S, T, n, m)
  H := Intseq(Hash(message),2);
  Si := Matrix(F2,n,1,[0 : k in [1..n]]);
  found_inverse := false;
  iter := 1;
  while found_inverse eq false do
    D := Matrix(F2,n,1,[H[k] : k in [1..n]]);
    DxorSi := D + Si;    // addition in F2 is a xor operation.
    try
      Si := invert(DxorSi, univF, S, T, n, m);
      found_inverse := true;
    catch e
      print Transpose(DxorSi), " n'est pas inversible.";
      iter +:= 1;
    end try;
    H := Intseq(Hash(H),2);
  end while;
  return Si, iter;
end function;

check_signature := function(signature, message, public_key, nb_ite, m)
  H := Intseq(Hash(message),2);
  Si := signature;
  // D := Matrix(F2, nb_ite, n, [0 : k in [1..n*nb_ite]]);
  for i in [1..(nb_ite-1)] do
    // D[i] := Vector(F2,[H[k] : k in [1..n]]);
    H := Intseq(Hash(H),2);
  end for;
  D := Matrix(F2,m,1,[H[k] : k in [1..m]]);
  // for i in [(nb_ite-1)..0] do
  //   Si := Matrix(F2,n,1,[Evaluate(public_key, [Si[k]: k in [1..n]])[k] : k in [1..n]]) + D[i];
  // end for;
  Si := Matrix(F2,m,1,[Evaluate(public_key, [Si[l][1]: l in [1..n]])[k] : k in [1..m]]) + D;
  if Si eq Matrix(F2,m,1,[0 : k in [1..m]]) then
    return "La signature est valide.";
  else
    return "La signature n'est pas valide.";
  end if;
end function;

message := [Random(F2) : k in [1..n]];  // is a list
print("Message : ");
Matrix(F2,1,n,message);
cipher_vinegars := [Random(F2) : k in [1..v]];
print "Variables vinaigres utilisées pour le chiffrement :", Matrix(1,v,cipher_vinegars);
cipher_m := cipher(message, public_key, cipher_vinegars, m);  // is a vertical matrix
print("Message chiffré : ");
Transpose(cipher_m);

// MPF2n_cipher_m := &+ [cipher_m[k]*a^(k-1) : k in [1..n]];
// MPF2n_cipher_m;

// fed_m := apply_F(message, univF);
// Roots(univF-fed_m);

inverted_cipher_m, inverted_cipher_m_vinegars := invert(cipher_m, univF, S, T, n, m, v);
print("Inverse du message chiffré : ");
Transpose(inverted_cipher_m);
// print "Ses vinaigres : ", inverted_cipher_m_vinegars;

// verification :
print("Chiffrement de l'inverse du message chiffré : ");
Transpose(cipher([inverted_cipher_m[k][1] : k in [1..n]], public_key, [inverted_cipher_m[k][1] : k in [n+1..n+v]], m));
// Transpose(cipher([inverted_cipher_m[k][1] : k in [1..n]], public_key, inverted_cipher_m_vinegars, m));

// // nb_ite := 4;
// m_signature, m_sign_iters := sign(message, univF, S, T, n, m);
// if m_sign_iters eq 1 then
//   print "signature du message, en 1 itération : ";
// else
//   print "signature du message, en ", m_sign_iters, " itérations : ";
// end if;
// Transpose(m_signature);
//
// // Signature verification :
// verif := check_signature(m_signature, message, public_key, m_sign_iters, m);
// print verif;
