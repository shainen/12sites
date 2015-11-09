(* ::Package:: *)

(* ::Section:: *)
(*All*)


(* ::Subsection:: *)
(*Constants*)


tmax=100;
steps=500;
times=Range[0,tmax,tmax/(steps-1)];


runs=10;


length=12;


bsites=Range[1,length-1,2];


j=-1;


fieldsW10={-6.810118375580723`,5.399321183414791`,7.047572832814368`,-4.414079687154078`,-8.41626615919514`,7.9393892160016355`,-5.806999450409989`,-8.53697581757193`,0.6676914555529989`,-2.5431706107186014`,6.844895559224515`,3.891957559769441`};


fieldsW5={-3.4050591877903615`,2.6996605917073957`,3.523786416407184`,-2.207039843577039`,-4.20813307959757`,3.9696946080008177`,-2.9034997252049943`,-4.268487908785965`,0.33384572777649946`,-1.2715853053593007`,3.4224477796122574`,1.9459787798847206`};


(* ::Subsection:: *)
(*Dyn funcs*)


add3[num_]:=Mod[num-1,3]+1


addl[num_]:=Mod[num-1,length]+1


bdot[s_,a_,d_,ham_]:=Total[D[ham,#1](#2)&@@@{{cS[addl[s]][add3[a+1]][t],-cB[addl[s]][add3[a+2],add3[d]][t]},{cS[addl[s]][add3[a+2]][t],cB[addl[s]][add3[a+1],add3[d]][t]},{cS[addl[s+1]][add3[d+1]][t],-cB[addl[s]][add3[a],add3[d+2]][t]},{cS[addl[s+1]][add3[d+2]][t],cB[addl[s]][add3[a],add3[d+1]][t]},{cB[addl[s]][add3[a+1],add3[d]][t],cS[addl[s]][add3[a+2]][t]/4},{cB[addl[s]][add3[a+2],add3[d]][t],-cS[addl[s]][add3[a+1]][t]/4},{cB[addl[s]][add3[a],add3[d+1]][t],cS[addl[s+1]][add3[d+2]][t]/4},{cB[addl[s]][add3[a],add3[d+2]][t],-cS[addl[s+1]][add3[d+1]][t]/4}}]


sdot[s_,a_,ham_]:=Total[D[ham,#1](#2)&@@@{{cS[addl[s]][add3[a+1]][t],cS[addl[s]][add3[a+2]][t]},{cS[addl[s]][add3[a+2]][t],-cS[addl[s]][add3[a+1]][t]}}~Join~Flatten[Table[{{cB[addl[s]][add3[a+1],d][t],cB[addl[s]][add3[a+2],d][t]},{cB[addl[s]][add3[a+2],d][t],-cB[addl[s]][add3[a+1],d][t]}},{d,3}],1]~Join~Flatten[Table[{{cB[addl[s-1]][d,add3[a+1]][t],cB[addl[s-1]][d,add3[a+2]][t]},{cB[addl[s-1]][d,add3[a+2]][t],-cB[addl[s-1]][d,add3[a+1]][t]}},{d,3}],1]]


(* ::Subsection:: *)
(*eqns*)


hamself[ss_]:=fieldsW5[[addl[ss]]]cS[addl[ss]][3][t]


sscoup[ss_]:=j(cS[addl[ss]][1][t]cS[addl[ss+1]][1][t]+cS[addl[ss]][2][t]cS[addl[ss+1]][2][t]+cS[addl[ss]][3][t]cS[addl[ss+1]][3][t])


bcoup[ss_]:=j(cB[addl[ss]][1,1][t]+cB[addl[ss]][2,2][t]+cB[addl[ss]][3,3][t])


hamcoupsu4[ss_]:=If[MemberQ[bsites,addl[ss]],bcoup[addl[ss]],sscoup[addl[ss]]]


hamcoupsu2[ss_]:=sscoup[addl[ss]]


eqss4=Table[cS[addl[ss]][sp]'[t]==sdot[addl[ss],sp,hamself[addl[ss]]+hamcoupsu4[addl[ss-1]]+hamcoupsu4[addl[ss]]],{ss,length},{sp,3}];


eqsb4=Table[cB[addl[ss]][sp1,sp2]'[t]==bdot[addl[ss],sp1,sp2,hamself[addl[ss]]+hamself[addl[ss+1]]+hamcoupsu4[addl[ss]]+hamcoupsu4[addl[ss-1]]+hamcoupsu4[addl[ss+1]]],{ss,bsites},{sp1,3},{sp2,3}];


eqall4=Flatten[{eqss4,eqsb4}];


eqss2=Table[cS[addl[ss]][sp]'[t]==sdot[addl[ss],sp,hamself[addl[ss]]+hamcoupsu2[addl[ss-1]]+hamcoupsu2[addl[ss]]],{ss,length},{sp,3}];


eqall2=Flatten[{eqss2}];


(* ::Subsection:: *)
(*Inits*)


initspin={2,2,2,2,2,1,2,1,1,1,1,1};


random[mean_,var_]:=If[var!=0,RandomVariate[NormalDistribution[mean,Sqrt[var]]],mean]


(* ::Subsubsection:: *)
(*spins*)


mean[op_,vec_]:=vec\[Conjugate].op.vec


cov[op1_,op2_,vec_]:=vec\[Conjugate].(op1.op2+op2.op1).vec/2-vec\[Conjugate].op1.vec vec\[Conjugate].op2.vec


spinmean=Table[mean[PauliMatrix[sp]/2,#],{sp,3}]&/@{{1,0},{0,1}};


spincov=Table[cov[PauliMatrix[sp1]/2,PauliMatrix[sp2]/2,#],{sp1,3},{sp2,3}]&/@{{1,0},{0,1}};


initsS:=Table[cS[addl[ss]][sp][0]==random[spinmean[[initspin[[addl[ss]]],sp]],spincov[[initspin[[addl[ss]]],sp,sp]]],{ss,length},{sp,3}]


(* ::Subsubsection:: *)
(*bispins*)


bmat[s1_,s2_]:=KroneckerProduct[PauliMatrix[s1],PauliMatrix[s2]]/If[s1==0||s2==0,2,4]


vecud[s1_,s2_]:=Flatten[Normal[KroneckerProduct[SparseArray[{initspin[[addl[s1]]]}->1,{2}],SparseArray[{initspin[[addl[s2]]]}->1,{2}]]]]


su4matrices=Join[bmat[#,0]&/@Range[3],bmat[0,#]&/@Range[3],Flatten[Outer[bmat,Range[3],Range[3]],1]];


su4varnames[ss_]:=Flatten[{cS[addl[ss]]/@Range[3],cS[addl[ss+1]]/@Range[3],Outer[cB[addl[ss]],Range[3],Range[3]]}]


matmean[op_,vec_]:=vec\[Conjugate].op.vec


bimean[ss_]:=matmean[#,vecud[addl[ss],addl[ss+1]]]&/@su4matrices


matcov[op1_,op2_,vec_]:=vec\[Conjugate].(op1.op2+op2.op1).vec/2-vec\[Conjugate].op1.vec vec\[Conjugate].op2.vec


covmat[ss_]:=Outer[matcov[#1,#2,vecud[addl[ss],addl[ss+1]]]&,su4matrices,su4matrices,1]


rotmat=Normalize/@Eigenvectors[covmat[addl[#]]]&/@Range[length];


rotcov=Eigenvalues[covmat[addl[#]]]&/@Range[length];


rotmean=Table[rotmat[[ss]].bimean[addl[ss]],{ss,length}];


initsB:=(
initsrot=Table[random[rotmean[[ss,bv]],rotcov[[ss,bv]]],{ss,length},{bv,15}];
initsorigbasis=MapThread[Dot,{Transpose[rotmat,{1,3,2}],initsrot},1];
Table[su4varnames[addl[ss]][[bi]][0]==initsorigbasis[[ss,bi]],{ss,bsites},{bi,15}]
)


(* ::Subsection:: *)
(*run TWA*)


eachTWA4=Table[solv=NDSolveValue[Flatten[{eqall4,initsB}],Flatten[Table[cS[addl[ss]][sp],{ss,length},{sp,3,3}]],{t,0,tmax}];{(Through[solv[#]]&/@times)\[Transpose],Total[(Through[solv[#]]Through[solv[0]]&/@times)\[Transpose]]/length},{rr,runs}];
fullTWA4=Total[eachTWA4]/runs;
sqTWA4=Total[eachTWA4^2]/runs;


(*eachTWA2=Table[solv=NDSolveValue[Flatten[{eqall2,initsS}],Flatten[Table[cS[addl[ss]][sp],{ss,length},{sp,3,3}]],{t,0,tmax}];{(Through[solv[#]]&/@times)\[Transpose],Total[(Through[solv[#]]Through[solv[0]]&/@times)\[Transpose]]/length},{rr,runs}];
fullTWA2=Total[eachTWA2]/runs;
sqTWA2=Total[eachTWA2^2]/runs;*)


mmu=MaxMemoryUsed[]/10.^6;


Save["12site.dat",{mmu,(*fullTWA2,sqTWA2,*)fullTWA4,sqTWA4}];
