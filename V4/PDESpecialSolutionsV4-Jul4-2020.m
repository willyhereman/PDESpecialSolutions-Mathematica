
(* ::Package: PDESpecialSolutionsV4-Jul4-2020.m: *)

(* Last updated by Hereman on July 4, 2020 at 14:30 in Boulder *)
(* Reason: *)
(* Also added a right hand side (== 0) in the output of the translation of the nonlinear PDE *) 
(* into the nonlinear ODE. *)
(* Changes: see WH: Jul/04/2020 *)

(* ::Title:: *)
(* Based on PDESpecialSolutionsV4-Mar30-2020-RK-WH.m. When further revision is finished, code will be PDESpecialSolutionsV5.m *)

(* ::Text:: *)
(* Layout updated and modified for Mathematica versions up to 12 *)
(* by Robert Kragler (March 17, 2020) *)

(* ::Section::Closed:: *)
(* Information *)

(* Changes see: WH:03/30/2020 and RK 13.03.2020 *)
(* Starting from version received from Robert Kragler, *)
(* last updated: March 30, 2020 at 21:40 by Hereman in Boulder *)

(* Previously updated: September 24, 2019 at 12:23am by Hereman in Boulder *)
(* Code PDESpecialSolutions-V4-Sep24-2019.m *)
(* Based on PDESpecialSolutionsV3n-June13-2017 *)
(* Changes: see WH:09/24/2019 *)
(* Reason: Improve the symbolic test of an exact solution in sech form *)

(* Previously updated: March 21, 2010 at 15:40 by Hereman in Boulder *)

(* Purpose: replace the old AnalyzeAndSolve -- dated January 8, 2010 with Doug Baldwin new AnalyzeAndSolve 
   -- dated March 13, 2010 Fix various bugs. Corrections are marked with WH:03/17/2010  *)

(* Previously updated: January 8, 2010 by Douglas Baldwin and Willy Hereman in Boulder at 16:50 *)
(* See DB:01/08/2010 Added Version 7.0+ check. *)

(* Previously updated: January 5, 2010 by Hereman in Boulder at 17:18 *)
(* Avoid the duplication problem that comes from the symbolic test; *)
(* changes marked with WH:01/05/2010 *)

(* ************************************************************************ *)
(* 
: Title : PDESpecialSolutionsV4-Jul4-2020.m 
*  : Authors : Douglas Baldwin, Unal Goktas, and Willy Hereman.
*    Department of Mathematical and Computer Sciences
*    Colorado School of Mines
*    Golden, Colorado 80401-1887, U.S.A.
*    Contact email: whereman@mines.edu or douglas@douglasbaldwin.com
*    with input from Robert Kragler 
*  : Last updated : Saturday, July 4, 2020 at 14:20 by Hereman  
*  : Previously updated : Monday, March 30, 2020 at 21:30 by Hereman  
*  : Based on update : Friday, January 8, 2009 at 16:50 by Hereman 
*  : Previous update : Sunday, December 13, 2009 at 23:30 by Goktas
                       and on January 23, 2009 by Hereman
*  : Based on code February 28, 2005 by Baldwin, Goktas, and Hereman
*  : Summary : Solves systems of nonlinear PDEs in terms of the hyperbolic
*    functions Tanh, Sech, and combinations of Sech and Tanh.
*  : Also computes exact solutions in terms of the Jacobi elliptic Cn and Sn 
     functions.
*  : Warnings : This package uses the assumption that Sqrt[a^2] -> a, etc.
*    (see mySimplificationRules below) when simplifying. 
*)

(* ************************************************************************ *)

(* Algorithms and implementation by Douglas Baldwin, Unal Goktas(WRI) and Willy Hereman. *)
(* Copyright 2001 *)

(* ::Section::Closed:: *)
(*BeginPackage*)

BeginPackage["Calculus`PDESpecialSolutions`"];
Unprotect[PDESpecialSolutions];

(* ::Section::Closed:: *)
(*Usage Messages*)

(* ::Subsubsection::Closed:: *)
(*Usage : *)

PDESpecialSolutions::usage = 
"PDESpecialSolutions[eqns, funcs, vars, params, opts] solves a system of
nonlinear partial differential equations (PDEs) for funcs, with
independent variables vars and non-zero parameters params." ;

(* ::Subsubsection::Closed:: *)
(*Messages : *)

PDESpecialSolutions::poly = "This system must be a polynomial of fixed order.";

PDESpecialSolutions::form = "The user entered form is not valid.";

PDESpecialSolutionsmSolver::freedom = "Freedom exists in this system, as `1` 
are both dominant powers in expression `2`.";

PDESpecialSolutions`dominantBehavior::freevalues = "The solution(s) `1` 
do not fix all the values of \!\(M\_i\).  
We will now generate all the possible values for the free \!\(M\_i\) up to 
the user option MaxDegreeOfThePolynomial which is set to 3 by default, 
but can be any non-negative integer.";

PDESpecialSolutions`dominantBehavior::underdetermined = 
"There is too much freedom in choosing the values of \!\(M\_i\). 
We will now generate all the possible values for the free \!\(M\_i\)
from zero to the user option MaxDegreeOfThePolynomial (with default 3),
but can be any integer.";

PDESpecialSolutionsmSolver::DegreeOfThePolynomial = "Algorithm continuing with
user given degree of the polynomial `1`.";

PDESpecialSolutionsmSolver::remove = "The potential solutions `1` 
are being removed because they are 
(i) negative, (ii) contain freedom, (iii) fail to balance highest exponent 
terms from two different terms in the original system.
If \!\(M\_i\) < 0, then the transform u -> 1/v might result in a system that
PDESpecialSolutions may be able to solve.";

PDESpecialSolutionsBuildSystem::fail = "The systems of equations was
inconsistent under the assumption that \!\(a\_\(i,M\_i\) \[NotEqual] 0\), 
please check the \!\(M\_i\) values by hand.";

PDESpecialSolutions::solve = "The algorithm failed while attempting to find 
the coefficients for the polynomial solution.";

(* ::Section::Closed:: *)
(* Options Definitions *)

(* WH:01/23/2009 NumericTest is set to True by default,  SymbolicTest is also set to True by default *)

Options[PDESpecialSolutions] =
  { Verbose -> False, 
    Form -> tanh, 
    NumericTest -> True, 
    SymbolicTest -> True, 
    InputForm -> False, 
    DegreeOfThePolynomial -> {},
    MinDegreeOfThePolynomial -> 1, 
    MaxDegreeOfThePolynomial -> 3, 
    SolveAlgebraicSystem -> True,
    HighestOrderFirst -> False,
    mSolverVerbose -> False
  };

sech=.; sechtanh=.; cn=.; sn=.; jacobisn=.; jacobicn=.;

(* added by RK 13.03.2020 *)
VersionDateTime :=                                         
   Module[{Months,year,month,day,hour,min,sec,hourS,minS},
          Months = {"January", "February", "March", "April", "May", "June", "July", "August", 
          "September", "October", "November", "December"};

          {year, month, day, hour, min, sec} = Date[];

          If[hour < 10, hourS = "0" <> ToString[hour],hourS = ToString[hour]];
          If[min  < 10, minS  = "0" <> ToString[min] , minS = ToString[min] ];

      Print["Mathematica V", StringTake[$Version, {1, 52}],         (* $Version for V11 *)
            "\ndate= ", Months[[month]]," ", day, ", ", year,"; time= ", hourS,":", minS, "h"]       
          ];

(* added by RK 13.03.2020 : Print routine with switch on|off *)
 print[onoff_String,prtList___]:= If[onoff==="On",Print[prtList]]      
(* extension of print routine; print["On", \[Ellipsis]] is totally switched off with global variable $print = "None"  *)
$print= "On";
 print[onoff_String,prtList___]:= If[$print != "None", If[onoff==="On",Print[prtList]],Null ]  

(* added by RK 13.03.2020 *)
cRule= {c[i_]^(p_:1)-> Subscript[c,i]^p, phase->\[Phi] };

cFwrap= Column[#,ItemSize->{Automatic,Automatic}]& ; 

tab[n_]:= Table["\t",{n}]/.{List -> StringJoin};

(* ::Section::Closed:: *)
(*Begin  package "PDESpecialSolutions" in Context`Private*)

(* ::Subsubsection::Closed:: *)
(* (1 ) : PDESpecialSolutions, make all arguments to lists *)

Begin["`Private`"];

(* If called with non-lists, makes them lists. *)

PDESpecialSolutions[eqns_?(!ListQ[#]&), funcs_, vars_, param_, opts___?OptionQ]:=
  PDESpecialSolutions[{eqns}, funcs, vars, param, opts]

PDESpecialSolutions[eqns_, funcs_?(!ListQ[#]&), vars_, param_, opts___?OptionQ]:=
  PDESpecialSolutions[eqns, {funcs}, vars, param, opts]

PDESpecialSolutions[eqns_, funcs_, vars_?(!ListQ[#]&), param_, opts___?OptionQ]:=
  PDESpecialSolutions[eqns, funcs, {vars}, param, opts]

PDESpecialSolutions[eqns_, funcs_, vars_, param_?(!ListQ[#]&), opts___?OptionQ]:=
  PDESpecialSolutions[eqns, funcs, vars, {param}, opts]
(* ************************************************************************ *)

(* ::Subsubsection::Closed:: *)
(* (2 ) : main procedure : PDESpecialSolutions*)

(* Start of function PDESpecialSolutions. *)

PDESpecialSolutions[eqns_List, funcs_List, vars_List, param_List, 
  opts___?OptionQ]:=
  Block[
    {testarg = FreeQ[MapAll[Expand, eqns], (Power[b__, a__] /; 
         (!FreeQ[a, _Symbol] | MemberQ[b, _Real | _Integer]))],
     theForm =
       ToExpression[
         ToLowerCase[
           ToString[Form /. {opts} /. Options[PDESpecialSolutions]]
         ]
       ] /. {jacobisn -> sn, jacobicn -> cn},
     VerboseTest = Verbose /. {opts} /. Options[PDESpecialSolutions],
     time = TimeUsed[],
     system,
     (* WH: Jul/04/2020 added local variable systemForm *)
     systemForm, 
     mSoln,
     newSystem,
     solution
    }, (* Protected Local Variables *)

  If[!testarg, Message[PDESpecialSolutions::poly]];
  (
    (* If verbose, prints system. *)

(* WH:03/30/2020 Robert Kragler RK needed modification for printout of equations *)
    If[VerboseTest,
      Print["The given system of differential equations is: " ];
       Print[ 
       (* modification for Mma > V7 , RK 13.3.2020 *)                                               
        TableForm[eqns /.                                        
          { Derivative[n__][F_][x__] :> Subscript[F, SequenceForm @@ 
                Flatten[ Table[#[[1]], {#[[2]]} ]& /@ Transpose[{{x}, {n}}] ] ],
            Sequence @@ ((# -> Head[#])& /@ funcs), funcs -> Head[funcs]
          }
        ]
      ]
    ];    

    (* Step 1 in the paper. *)
    (* Transforming the PDE into a nonlinear ODE in $T=Tanh$ or $S=Sech$ *)
   If[VerboseTest,
   Print["Transforming the differential equation(s) into a nonlinear ODE in "<>
        ToString[
          (theForm /. 
            {tanh -> "T=Tanh", sech -> "S=Sech", sechtanh -> "S=Sech", 
             cn -> "CN=JacobiCN", sn -> "SN=JacobiSN"}
          )
        ]
      ]
   ];

    system = 
      PDESpecialSolutionsVarChange[
        eqns /. (a__ == b__):>(a-b), 
        funcs, 
        vars, 
        opts
      ];
      
(* WH:Jul/04/2020 system did not have proper right hand side (== 0) *)
   
   systemForm = Map[# == 0&, system]; 

   If[VerboseTest,
      Print[CleanUpFunction[systemForm /. myTrackingVariable[_]->1]];
      Print["Time Used:", TimeUsed[]-time]
    ];
 
 (* was 
    If[VerboseTest,
      Print[CleanUpFunction[system /. myTrackingVariable[_]->1]];
      Print["Time Used:", TimeUsed[]-time]
    ];
*)

    time = TimeUsed[];

    (* Step 2 in the paper. *)
    (* Determining the maximal degree of the polynomial solutions. *)
    If[VerboseTest,
      Print["Determining the maximal degree of the polynomial solutions."]
    ];

    mSoln =
      Internal`DeactivateMessages[
        PDESpecialSolutionsmSolver[system, theForm, opts], 
        Solve::svars
      ];

    If[VerboseTest,
      Print[CleanUpFunction[mSoln]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step 3 in the paper. *)
    (* Deriving the algebraic system for the coefficients $a_{ij}, b_{ij}$. *)

    (* WH:01/05/2010 moved the print statement lower *)
    (* 
    If[VerboseTest,
      Print["Deriving the nonlinear algebraic system for the coefficients."]
    ];

    *)
    {mSoln, newSystem} = 
      PDESpecialSolutionsBuildSystem[mSoln, system, vars, param, opts];

    If[VerboseTest,
      Print["Deriving the nonlinear algebraic system for the coefficients."]
    ];

    If[VerboseTest,
      Print["The nonlinear algebraic system is"];
      Print[CleanUpFunction[newSystem /. myTrackingVariable[_]->1]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* DB:03/21/2003 Output algebraic system. *)
    If[!(SolveAlgebraicSystem /. {opts} /. Options[PDESpecialSolutions]),
      Return[CleanUpFunction[newSystem]];
    ];

    (* Step 4 in the paper. *)
    (* Solving the nonlinear parameterized algebraic system. *)
    If[VerboseTest,
      Print["Solving the nonlinear algebraic system."]
    ];

    solution = 
        Algebra`AnalyzeAndSolve`AnalyzeAndSolve @@ #& /@ newSystem;
    If[Length[Flatten[solution]] === 0,
      Message[PDESpecialSolutions::solve];Return[{}];
    ];

    (* Reformat the output after Unal's change of AnalyzeAndSolve's output *)
    (* DB:11/27/2002 *)
    solution = 
      (# /. List[(a_List)..] :> a)& /@ #& /@ solution; 

    If[VerboseTest,
      Print[CleanUpFunction[solution]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step 5 in the paper. *)
    (* Building and testing the solitary wave solutions. *)
    If[VerboseTest,
      If[( !(NumericTest /. {opts} /. Options[PDESpecialSolutions]) &&
           !(SymbolicTest /. {opts} /. Options[PDESpecialSolutions]) ), 
        Print["Building the travelling wave solutions (without testing)."],
        Print["Building and (numerically and/or symbolically) testing "<>
          "the solutions."]
      ]
    ];

    solution = 
      PDESpecialSolutionsBuildSolutions[solution, mSoln, 
        eqns, funcs, vars, param, opts];

    (* start if 10 *)
    If[VerboseTest,
      Print["Time Used:", TimeUsed[]-time];
      Print[];
      (* WH:01/05/2010 adjusted the print statements *)
      Which[
        ( ( NumericTest /. {opts} /. Options[PDESpecialSolutions] ) &&
          !( SymbolicTest /. {opts} /. Options[PDESpecialSolutions] ) ),
        Print["The final solutions were only tested numerically."],
        ( (SymbolicTest /. {opts} /. Options[PDESpecialSolutions]) &&
          !( NumericTest /. {opts} /. Options[PDESpecialSolutions] ) ),
        Print["The final solutions were only tested symbolically."],
        ( ( NumericTest /. {opts} /. Options[PDESpecialSolutions] ) && 
        ( SymbolicTest /. {opts} /. Options[PDESpecialSolutions] ) ),
        Print["The final solutions were tested both numerically "<> 
              "and symbolically."],
        ( !( NumericTest /. {opts} /. Options[PDESpecialSolutions] ) &&
          !( SymbolicTest /. {opts} /. Options[PDESpecialSolutions] ) ),
         Print["The list of possible final solutions (without "<>
         "testing them numerically or symbolically):"]
      ] (* end of which *)
     ]; (* end if 10 *)

    (* Returns solutions to user. *)
    Return[
      If[InputForm /. {opts} /. Options[PDESpecialSolutions], 
        InputForm[CleanUpFunction[solution]],
        CleanUpFunction[solution]
      ]
    ]
  ) /; testarg
 ]; 
 (* end of block PDESpecialSolutions *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (3 ) : procedure : PDESpecialSolutionsVarChange*)


(* : Title : PDESpecialSolutionsVarChange *)
(* : Author : Douglas Baldwin *)
(* : Input : The equation list (F[i][x,y,z,t]) and the form tanh. *)
(* : Output : The system in the form u[i][T] depending on whether 
     it is tanh. *)
(* : Summary : Converts from real space-time domain to u[i][T]. *)

PDESpecialSolutionsVarChange[eqns_List, funcs_List, vars_List,
    opts___?OptionQ]:=
    Block[{Form, (* The form of the wanted solution. *)
        funcRules, (* conversion from user functions *)
        i=0, (* Iterator for myTrackingVariables *)
        eqList, (* The list of equations, in a usable form *)
        system, (* The system after transformation to ODE in T *)
        phi (* A temporary function. *)
        }, (* Protected Local Variables *)

     (* Sets the Form from user options *)
     Form =
       ToExpression[
         ToLowerCase[
           ToString[Form /. {opts} /. Options[PDESpecialSolutions]]
         ]
       ] /. {jacobisn -> sn, jacobicn -> cn};

    (* If form isn't correct, it sends a message and aborts. *)
    If[!(Or @@ ((Form === #)& /@ {tanh, sech, sechtanh, cn, sn})),
      Message[PDESpecialSolutions::form]; Abort[]
    ];

    (* Creates a set of rules to converts the users functions *)
    (* (e.g., u[n,t]) to varChangeFunction[i][n,t]. *)
    funcRules = 
      Table[
        Head[funcs[[i]] ] -> varChangeFunction[Form][i],
        {i, Length[funcs]}
      ];

    (* Adds tacking variables which will be used in the mSolve *)
    (* function to check for false balances coming form a single *)
    (* term. *)
    eqList = 
      If[Head[#] === Plus, 
        Plus @@ ((myTrackingVariable[++i]*#) & /@ List @@ #),
        myTrackingVariable[++i]*#] & /@ Expand[eqns];

    (* Converts the user functions to varChangeFunction[i]. *)
    eqList = eqList //. funcRules;

    (* Changes the space of the functions. *)
    system = eqList /. 
      {
      varChangeFunction[form_][n_][var__] :> 
        phi[form][n][
          Sum[c[i]*{var}[[i]], 
            {i, Length[{var}]}
          ]
        ], 
       Derivative[temp__][varChangeFunction[form_][n_]][var__] :>  
         (
           D[
            phi[form][n][
              Sum[c[i]*{var}[[i]], 
                {i, Length[{var}]}
              ]
            ],
            Sequence @@ Transpose[{{var}, {temp}}]
           ]
         )
      };

    (* Parameterizes the sequence $c_1 x+c_2 y+...\to\eta$ *)
    system = system /. 
      {
        phi[form_][n_][__] :> phi[form][n][eta],
        Derivative[i_][phi[form_][n_]][__] :> Derivative[i][phi[form][n]][eta]
      };

    (* Repeatedly applies the chain rule. *)
      system = system /. 
        {Derivative[a_][phi[tanh][n_]][eta] :> 
          Expand[
            Nest[(1-T^2)*D[#, T]&, 
              u[n][T], 
              a
            ]
          ], 
         phi[tanh][n_][eta] :> u[n][T],
         Derivative[a_][phi[sech][n_]][eta] :> 
            Expand[
              Nest[-(S*Sqrt[1-S^2])*D[#, S]&, 
                u[n][S], 
                a
              ]
            ], 
         phi[sech][n_][eta] :> u[n][S],
         Derivative[a_][phi[sechtanh][n_]][eta] :> 
            Expand[
              Nest[-(S*Sqrt[1-S^2])*D[#, S]&, 
                u[n][S], 
                a
              ]
            ], 
         phi[sechtanh][n_][eta] :> u[n][S],
         Derivative[a_][phi[cn][n_]][eta] :> 
            Expand[
              Nest[-Sqrt[1-mod-CN^2+2*mod*CN^2-mod*CN^4]*D[#, CN]&, 
                u[n][CN], 
                a
              ]
            ], 
         phi[cn][n_][eta] :> u[n][CN],
         Derivative[a_][phi[sn][n_]][eta] :> 
            Expand[
              Nest[Sqrt[1-SN^2-mod*SN^2+mod*SN^4]*D[#, SN]&, 
                u[n][SN], 
                a
              ]
            ], 
        phi[sn][n_][eta] :> u[n][SN]
        };

    system = (system /. (p_ -> q_) :> (p -> Expand[q]));

    (* Simplifies the system by removing extra (1-T^2)'s *)
    (* and T's from the system. *)
    system = 
      If[(# /. T->-1) === 0 && (# /. T->1) === 0, 
        Factor[#/(1-T^2)], Factor[#]]& /@ system;
    system = 
      If[(# /. T -> 0) === 0, 
        Factor[#/T], Factor[#]]& /@ system;
    system = 
      If[(# /. S -> 0) === 0, 
        Factor[#/S], Factor[#]]& /@ system;
    system = 
      If[(# /. S -> -1) === 0 && (# /. S->1) === 0, 
        Factor[#/Sqrt[1-S^2]], Factor[#]]& /@ system;
    system = 
      If[(# /. CN -> 0) === 0, 
        Factor[#/CN], Factor[#]]& /@ system;
    system = 
      If[(((# /. CN -> -1) === 0 && (# /. CN -> 1) === 0 ) &&
           (Factor[# /. CN -> Sqrt[-1+mod]/Sqrt[mod] ]) === 0), 
        Factor[#/Sqrt[1-mod-CN^2+2*mod*CN^2-mod*CN^4]], Factor[#]]& /@ system;
    system = 
      If[(# /. SN -> 0) === 0, 
        Factor[#/SN], Factor[#]]& /@ system;
    system = 
      If[(((# /. SN -> -1) === 0 && (# /. SN -> 1) === 0 ) &&
           (Factor[# /. SN -> 1/Sqrt[mod] ]) === 0 ), 
        Factor[#/Sqrt[1-SN^2-mod*SN^2+mod*SN^4]], Factor[#]]& /@ system;

    (* Returns the system back to the PDESpecialSolutions *)
    Return[(system /. (p_ -> q_) :> (p -> Factor[q]))];
  ]; (* end of block PDESpecialSolutionsVarChange *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (4a ) : procedure : PDESpecialSolutionsmSolver*)


(* : Title : PDESpecialSolutionsmSolver *)
(* : Author : Douglas Baldwin *)
(* : Date : Sunday, December 15, 2002 *)
(* : Input : The system generated by varChange. *)
(* : Output : The power of the polynomial solutions for u[i][T], id est 
     u[i][T] = a[1,0]+a[1,1]*T+a[1, 2]*T^2+...+a[1,n]*T^n. *)

PDESpecialSolutionsmSolver[system_List, theForm_, opts___?OptionQ] :=
  Module[{mSoln},
    mSoln = 
      { ToExpression[
          StringReplace[            
            ToString[DegreeOfThePolynomial /. {opts}],
            {"m" -> "Calculus`PDESpecialSolutions`Private`m",
             "n" -> "Calculus`PDESpecialSolutions`Private`n"
            }
          ]
        ]
      }; 
    Message[PDESpecialSolutionsmSolver::DegreeOfThePolynomial, 
      CleanUpFunction[mSoln]
    ];
    Return[mSoln];
   ] /; (DegreeOfThePolynomial /. {opts} /. 
     Options[PDESpecialSolutions]) =!= {};
     
   (* end of module PDESpecialSolutionsmSolver *)


(* ::Subsubsection::Closed:: *)
(* (4b ) : procedure : PDESpecialSolutionsmSolver*)


PDESpecialSolutionsmSolver[system_List, theForm_, opts___?OptionQ] :=
  Module[{mSolverDebug = (* Debugging Boolean flag *)
            (mSolverVerbose /. {opts} /. Options[PDESpecialSolutions]), 
          myTrackingVariableMax, (* Max Tracking Variable. *)
          funcRules, (* Replaces F with T, S, CN, SN, etc. *)
          eqnList, (* The result of the system generation function. *)
          mList0, mList, (* Lists of the powers of F in m_i. *)
          myMList, (* List of m_i's:  {m_1, m_2, m_3, ...} *)
          mRules, (* Rules for m_i, such as m_1 -> m_2. *)
          mSoln, mSoln0 (* List of explicit solutions for m_i. *)
         },

    (* Determines max{i : myTrackingVariables[i]} by *)
    (* applying a rule to system which sets myTrackingVariable *)
    (* in the process.  *)
    myTrackingVariableMax = 0;
    system /. myTrackingVariable[a_Integer] :> 
      myTrackingVariable[
        If[a > myTrackingVariableMax, 
           myTrackingVariableMax = a
          ]; 
      a];

    (* Sets up a list of rules for replacing the form of F. *)
    funcRules = {tanh -> T, sech -> S, sechtanh -> S, cn -> CN, sn -> SN};

    (* Breaks into parts P + Q Sqrt[...] and substitutes *)
    (* the ansatz chi F^{m_i} for u,v,...,w *)
    eqnList = 
      mSolve`SystemGeneration[system, theForm, myTrackingVariableMax, opts];

    If[mSolverDebug,
      Print["eqnList, System after ansatz substitution:"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Pulls off the expressions for m_i *)
    mList0 = mSolve`ListFormation[eqnList, theForm, 
                 funcRules, myTrackingVariableMax, opts];

    If[mSolverDebug,
      Print["mList0, Exponents of F before simplification:"];
      Print[CleanUpFunction[mList0]];
    ];

    (* If the form is of SechTanh, it uses the solution m_i=2, n_i=1 *)
    If[theForm === sechtanh,
      (* Sets mSoln so m_i = 2 and n_i = 1 *)
      mSoln = 
        {
          Flatten[
            Table[{m[i]->2, n[i]->1}, 
              {i, Length[system]}
            ]
          ]
        };

      (* Returns the solution. *)
      Return[mSoln];
    ];

    (* Removes expressions which cannot be the highest power *)
    (* by trackingVariable. *)
    mList = 
      Flatten[mSolve`Simplification[#, opts]& /@ #]& /@ mList0;

    If[mSolverDebug,
      Print["mList, mList0 after simplification:"];
      Print[CleanUpFunction[mList]];
    ];

    (* Forms a list of all the m_i. *)
    myMList = {};
    mList /. 
      m[i_Integer] :> (myMList = Append[myMList, m[i]];m[i]);
    myMList = Union[myMList];

    If[mSolverDebug,
      Print["The $m_i$s to be solved for are:"];
      Print[CleanUpFunction[myMList]];
    ];

    (* Solves the expressions of m_i for m_i *)
    mRules = mSolve`RulesSolver[#, myMList, opts]& /@ mList;

    If[mSolverDebug,
      Print["mRules, the solution iteration yields:"];
      Print[CleanUpFunction[mRules]];
    ];  

    (* Uses the previous results to determine *)
    (* explicit solutions for m_i. *)
    mSoln0 = mSolve`PowerSolver[mRules, myMList, opts];

    If[mSolverDebug,
      Print["mSoln, the possible solutions before pruning:"];
      Print[CleanUpFunction[mSoln0]];
    ];  

    (* DB:05/15/2004 New version from Painleve code. *)
    mSoln =   
      Join[ mSoln0, mSolve`FixFreeM[mSoln0, myMList, opts]];

    (* Remove bad solutions. *)
    mSoln  = 
      mSolve`SystemCleanUp[eqnList, mList, mSoln, 
                          myMList, theForm /. funcRules, opts ];

    (* DB:03/21/2003 Warn the user when potential solutions are removed. *)
    If[Length[Complement[Union[Sort /@ mSoln0], mSoln] ] > 0,
      StylePrint[
        "The potential solutions "<>
        ToString[ 
          InputForm[
            CleanUpFunction[
              Complement[Union[Sort /@ mSoln0], mSoln] 
            ] 
          ]
        ] <> 
        " are being removed because they are (i) negative, (ii) contain "<>
        "freedom, (iii) fail to balance highest exponent terms from two "<>
        "different terms in the original system.  If \!\(M\_i\) < 0, "<>
        "then the transform u -> 1/v might result in a system that "<>
        "PDESpecialSolutions may be able to solve.", 
        "Message"
      ];
    ];

    If[mSolverDebug,
      Print["mSoln, after being pruned:"];
      Print[CleanUpFunction[mSoln]];
    ];  

    (* If it doesn't find any find any solutions, it quits. *)
    If[Length[mSoln] === 0, 
      StylePrint[
        "The algorithm failed while attempting to find a positive values "<> 
        "of \!\(M\_i\).  The list of rules that constrain the system are " 
        <> ToString[ InputForm[ CleanUpFunction[mRules] ] ] <>
        ".  The original powers in \!\(M\_i\) are " <>
        ToString[ InputForm[ CleanUpFunction[mList] ] ] <>
        ". The package will now test all the possible solutions in the " <>
        "range MinDegreeOfThePolynomial to MaxDegreeOfThePolynomial.",
        "Message"    
      ];
      
      (* Generate all the possible solutions from -3 to -1. *)
      mSoln = 
        mSolve`SystemCleanUp[eqnList, 
          mList, 
          mSolve`GenerateAlternativeSolutions[
            myMList,
            opts
          ], 
          myMList, 
          theForm /. funcRules, 
          opts 
        ]
    ];

    (* If it doesn't find any find any solutions, it quits. *)
    If[Length[mSoln] == 0, 
      Abort[ ]
    ];

    If[mSolverDebug,
      Print["mSoln, the final version before being returned:"];
      Print[CleanUpFunction[mSoln]];
    ];  

    (* Returns the solutions. *)
    Return[mSoln];

  ] /; (DegreeOfThePolynomial /. {opts} /. 
     Options[PDESpecialSolutions]) === {};
     
  (* end of module PDESpecialSolutionsmSolver *)


(* ::Subsubsection::Closed:: *)
(* (5a ) : procedure : mSolve`SystemGeneration*)


(* Breaks up the system into the correct form. *)
mSolve`SystemGeneration[system_, theForm_, 
    myTrackingVariableMax_, opts___?OptionQ] :=
  Block[{SystemGenerationDebug = (* Debugging Boolean flag *)
            (mSolverVerbose /. {opts} /. Options[PDESpecialSolutions]), 
          sqrtRules, (* A set of rules for replacing what's *)
                     (* under the radical. *)
          mySystem, (* The system passed to the function after *)
                    (* transformation. *)
          eqnList (* The result which will be returned. *)
         },

    
    (* Sets up the way in which the system will be divided up *)
    (* in the next step, based on the Options set by the user. *)
    sqrtRules = 
      {tanh -> Null, 
       sech -> 1-S^2, 
       sechtanh -> 1-S^2,
       cn -> 1-mod-CN^2+2*mod*CN^2-mod*CN^4,
       sn -> 1-SN^2-mod*SN^2+mod*SN^4
      };
    
    (* DB:02/28/2005 Added new Coefficient function, for 5.0 compatibility. *)
    myCoefficient[p_Plus, q_, 0] := Plus @@ Select[p, FreeQ[#,q]&]; 
    myCoefficient[p_, q_, 0] := Plus @@ Select[{p}, FreeQ[#,q]&]; 
    myCoefficient[p_Plus, q_, 1] := Plus @@ Cases[p, z_. q -> z]; 
    myCoefficient[p_, q_, 1] := Plus @@ Cases[{p}, z_. q -> z]; 
    
    (* Breaks up system into P and Q, where system = P + Sqrt[...]*Q. *)
    mySystem = 
      {myCoefficient[#,Sqrt[theForm /. sqrtRules], 0]& /@ 
                     MapAll[Expand, system], 
       myCoefficient[#,Sqrt[theForm /. sqrtRules], 1]& /@ 
                     MapAll[Expand, system]};

    If[SystemGenerationDebug,
      Print["The system divided into P and Q, is: "];
      Print[CleanUpFunction[mySystem]];
    ];

    mySystem = mSolve`SimplifySystem[mySystem];

    If[SystemGenerationDebug,
      Print["The system after simplification is: "];
      Print[CleanUpFunction[mySystem]];
    ];

    (* Replaces the function u[i_] with a function in *)
    (* F^m[i] or F^n[i]. *)
    eqnList = 
      Expand[
        DeleteCases[
          Flatten[
            mySystem /. u[i_] :> Function[{F}, \[Chi][i]*F^m[i] ]
          ], 
          0
        ]
      ];

    If[SystemGenerationDebug,
      Print["The system after substitution of $chi F^{m_i}$"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Returns the list after substitution of the ansatz. *)
    Return[eqnList];

  ]; (* end of block mSolve`SystemGeneration *)


(* Simplifies the system by removing extra (1-T^2), (1-S^2), *)
(* S, T, etc. from the system. *)
mSolve`SimplifySystem[system_]:=
  Module[{mySystem = system},
    mySystem = 
      If[(# /. T->-1) === 0 && (# /. T->1) === 0, 
        Expand[#/(1-T^2)], Expand[#]]& /@ #& /@ mySystem;
    mySystem = 
      If[(# /. T->0) === 0, 
        Expand[#/T], Expand[#]]& /@ #& /@ mySystem;
    mySystem = 
      If[(# /. S->0) === 0, 
        Expand[#/S], Expand[#]]& /@ #& /@ mySystem;
    mySystem = 
      If[(# /. S->-1) === 0 && (# /. S->1) === 0, 
        Expand[#/Sqrt[1-S^2]], Expand[#]]& /@ #& /@ mySystem;
    mySystem = 
      If[(# /. CN -> 0) === 0, 
        Expand[#/CN], Expand[#]]& /@ mySystem;
    mySystem = 
      If[(((# /. CN -> -1) === 0 && (# /. CN -> 1) === 0 ) &&
           (Expand[# /. CN -> Sqrt[(-1+mod)/mod] ]) === 0 ), 
      Expand[#/Sqrt[1-mod-CN^2+2*mod*CN^2-mod*CN^4]], Expand[#]]& /@ mySystem;
    mySystem = 
      If[(# /. SN->0) === 0, 
        Expand[#/SN], Expand[#]]& /@ mySystem;
    mySystem = 
      If[(((# /. SN->-1) === 0 && (# /. SN->1) === 0 ) &&
           (Expand[# /. SN -> 1/Sqrt[mod] ]) === 0 ), 
        Expand[#/Sqrt[1-SN^2-mod*SN^2+mod*SN^4]], Expand[#]]& /@ mySystem;

    (* Returns the simplified system. *)
    Return[mySystem];
  
  ]; (* end of module mSolve`SimplifySystem *)


(* ::Subsubsection::Closed:: *)
(* (5b ) : procedure : mSolve`ListFormation*)


mSolve`ListFormation[eqnList0_, Form_, 
    funcRules_, myTrackingVariableMax_, opts___?OptionQ]:=
  Block[{ mPowerListFormationDebug = (* Debugging Boolean flag *)
            (mSolverVerbose /. {opts} /. Options[PDESpecialSolutions]), 
          eqnList = eqnList0,
          mList
         },

    eqnList = 
      ( Table[Coefficient[#, myTrackingVariable[i] ], 
          {i, 1, myTrackingVariableMax}
        ]& /@ eqnList0) /. 0:>Sequence[];

    If[mPowerListFormationDebug,
      Print["The system further divided, is: "];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Breaks up expressions into lists of terms. *)
    eqnList = 
      If[Head[#] === Plus, List @@ #, {#}]& /@ #& /@
        (eqnList /. (p_ -> q_) :> (p -> Expand[q]));

    If[mPowerListFormationDebug,
      Print["The system where + -> {} is:"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Pulls off the exponents of T and forms a list *)
    (* of expressions of the form {{{1+m[1]},{..}..}..}  *)
    (* DB:05/15/2004 moved Union. *)
    mList = 
      ( Union[
          Exponent[#, 
            Form /. funcRules 
          ]
        ]& /@ 
      #)& /@ eqnList;

    If[mPowerListFormationDebug,
      Print["The list of powers of F is:"];
      Print[CleanUpFunction[mList]];
    ];

   (* Returns the number of equations and the list of powers. *)
   Return[mList];
   
  ]; (* end of block mSolve`ListFormation *)


(* ::Subsubsection::Closed:: *)
(* (5c ) : procedure : mSolve`Simplification*)


mSolve`Simplification[mList0_, opts___?OptionQ]:=
  Module[{mPowerListSimplificationDebug = (* Debugging Boolean flag *)
            (mSolverVerbose /. {opts} /. Options[PDESpecialSolutions]), 
          mList, (* The list of powers. *)
          mListStructure (* Structure of powers. *)
         }, (* Protected Local Variables. *)

    (* The following lines breaks up the list of exponents *)
    (* of T and then removes invalid cases. *)

    (* Breaks up the expressions of $a+b \, m_i+c\, m_j+...$ *)
    (* where $a,b,c,...,i,j,k,...\in\mathbb{R}$ into lists. *)
    mList = 
      If[Head[#] === Plus, 
        List @@ #, 
        If[(Head[#] === m || Head[#] === n) || Head[#] === Times, 
          {#}, 
          #
        ]
      ]& /@ mList0;

    If[mPowerListSimplificationDebug,
      Print["Breaks up $a+b m_i+c m_j+...$ into lists:"];
      Print[CleanUpFunction[mList]];
    ];

    (* The following routine strips off the $a$ in the above *)
    (* expression and leaves only the underlying structure. *)
    mListStructure = Union[mList /. {a_Integer, b__}:>{b}];

    If[mPowerListSimplificationDebug,
      Print["The above sans $a$:"];
      Print[CleanUpFunction[mListStructure ]];
    ];

    (* Re-organizes the list of powers of T by the structure *)
    (* listed above. *)
    mList = 
      Cases[mList, {_, Sequence @@ #} | #]& /@ mListStructure;

    If[mPowerListSimplificationDebug,
      Print["The list of powers reorganized by structure:"];
      Print[CleanUpFunction[mList ]];
    ];

    (* Determines the maximum $a$ in each power of T *)
    mList = 
      {Max[# /. {a_, ___}:>If[IntegerQ[a], a, 0]& /@ #]}& /@ mList;

    If[mPowerListSimplificationDebug,
      Print["The list of powers after powers which cannot be "<>
            "the highest power are removed:"];
      Print[CleanUpFunction[mList ]];
    ];

    (* Creates a list of the maximum powers of T, such *)
    (* that all the members of the list are of the form *)
    (* $a_{\rm max}+b\,m_i+c\,m_j+...+d\,m_i\,m_j$ *)
    mList = 
      (Plus @@ Flatten[#])& /@ 
        Transpose[{mList, mListStructure}];

    If[mPowerListSimplificationDebug,
      Print["Formulates the powers back into the correct form:"];
      Print[CleanUpFunction[mList ]];
    ];

    (* Returns the simplified list. *)
    Return[mList];
 
 ]; (* end of module mSolve`Simplification *)


(* ::Subsubsection::Closed:: *)
(* (5d ) : procedure : mSolve`RulesSolver*)


mSolve`RulesSolver[mList0_, myMList_, opts___?OptionQ]:=
  Module[{rulesSolverDebug = (* Debugging Boolean flag *)
            (mSolverVerbose /. {opts} /. Options[PDESpecialSolutions]), 
          mList,
          eqnList,
          mRules (* List of rules from first solve. *)
         }, (* Protected local variables. *)

    (* Makes sure it is the simplest list possible *)
    (* for combinatorial purposes. *)
    mList = Union[mSolve`Simplification[mList0] ];

    If[rulesSolverDebug,
      Print["The mList used in Power Solver is"];
      Print[CleanUpFunction[mList]];
    ];    

    (* Forms a list of equations to be solved for m_i. *)
    eqnList =   
      Flatten[
        Map[
          Thread[
            Table[#[[1]], {Length[#] -1} ] == Drop[#, 1]
          ]&,
          Table[Drop[mList, i], 
            {i, 0, Length[mList] - 2}
          ]
        ],
        1
      ];

    If[rulesSolverDebug,
      Print["The Equations to be solved first"];
      Print[CleanUpFunction[eqnList]];
    ];    

    (* Does the first run of solving. *)
    mRules = 
      Union[
        Flatten[
          Solve[#, myMList]& /@ eqnList
        ]
      ];

    If[rulesSolverDebug,
      Print["The first set of solutions are"];
      Print[CleanUpFunction[mRules]];
    ];    

    Return[mRules];

  ]; (* end of module mSolve`RulesSolver *)


(* ::Subsubsection::Closed:: *)
(* (5f) : procedure : mSolve`PowerSolver*)


mSolve`PowerSolver[mRules0_, myMList_, opts___?OptionQ]:=
  Module[{powerSolverDebug = (* Debugging Boolean flag *)
            (mSolverVerbose /. {opts} /. Options[PDESpecialSolutions]), 
          mRules = Sort[mRules0, (Length[#1] < Length[#2])&],
          numberOfEquations = Length[myMList]
         }, (* Protected local variables. *)

    If[powerSolverDebug,
      Print["The mRules used in Power Solver (sorted from " <>
            "shortest to longest) is:"];
      Print[CleanUpFunction[mRules]];
    ];    

    (* A little warning message if there is a combinatorial explosion. *)
    If[Binomial[Length[Flatten[ mRules ] ], numberOfEquations] > 100,
      CellPrint[
        Cell["Formulating and solving up to " <>
          ToString[ Binomial[Length[Flatten[ mRules ] ], 
                    numberOfEquations] ] <>
          " systems of equations.  Please be patient.",
          "Message"
        ]
      ];
    ];

    (* Forms a list of equations to be solved for m_i. *)
    eqnList = 
      Outer[List, Sequence @@ (mRules /. Rule->Equal)];

    (* Since Outer creates a list numberOfEquations deep, we *)
    (* drop it down into the correct form. DB:05/20/2003 *)
    eqnList = 
      Partition[ Flatten[ eqnList ], numberOfEquations ];
    
    If[powerSolverDebug,
      Print["The next set of equations to be solved are:"];
      Print[CleanUpFunction[eqnList]];
    ];   

    (* Takes these solutions and uses them to find *)
    (* actual integer solutions to $m_i$ *)
    mSoln = 
      Union[
        Sequence @@ 
          Solve[#, myMList]& /@ eqnList
      ];

    If[powerSolverDebug,
      Print["The solutions are:"];
      Print[CleanUpFunction[mSoln]];
    ];

   (* Returns the solutions *)
   Return[mSoln];

  ]; (* end of module mSolve`PowerSolver *)


(* ::Subsubsection::Closed:: *)
(* (5g ) : procedure : mSolve`SystemCleanUp*)


mSolve`SystemCleanUp[eqnList0_, mList_, mSoln0_, 
    myMList_, F_, opts___?OptionQ]:=
  Module[{systemCleanUpDebug = (* Debugging Boolean flag *)
            (mSolverVerbose /. {opts} /. Options[PDESpecialSolutions]), 
          mSoln = Union[Sort /@ mSoln0], (* A local version of mSoln0. *)
          chiList = {}, (* The list of chi constraints. *)
          eqnList, (* A local copy of the equations. *)
          numberOfEquations = Length[eqnList0] (* The number of equations. *)
         }, (* Protected local variables. *)

     (* Applies the solutions to the expressions of m_i. *)
     mSoln = 
      Transpose[{(mList //. #)& /@ mSoln, mSoln}];

     If[systemCleanUpDebug,
       Print["The expressions of m_i after possible " <>
             "solution substitution:"];
      Print[CleanUpFunction[mSoln]];
    ];

    mSoln = 
      mSoln /. 
        {a_List, {(_Rule)..}} :> Sequence[] /;
          Not[ And @@ (FreeQ[ a, #] & /@ myMList  ) ];

    If[systemCleanUpDebug,
      Print["mSoln, after the underdetermined systems are removed:"];
      Print[CleanUpFunction[mSoln]];
    ];

    (* Removes solutions that do not balance at least two independent *)
    (* Terms in the original system. *)
    mSoln = 
      mSoln /.
        { {a_List, b : {(_Rule) ..}} :> 
            b  /; And @@ ((Length[ Cases[#, Max[#]] ] >= 2)& /@ a),
          {a_List, b : {(_Rule) ..}} :> 
            Sequence[]
        };

    If[systemCleanUpDebug,
      Print["mSoln, after power balances are checked:"];
      Print[CleanUpFunction[mSoln]];
    ];

    (* Removes solutions with any of the $M_i = 0$. DB:05/25/2003 *)
    mSoln = 
      mSoln /. 
        a : {(_Rule) ..} :> 
          Sequence[] /; Or @@ ( #[[2]] === 0 & /@ a );

    If[systemCleanUpDebug,
      Print["mSoln, after zero solutions are removed:"];
      Print[CleanUpFunction[ mSoln ]];
    ];
    
    (* If we are dealing with a system of equations, than we remove negative *)
    (* and rational solutions for the dominate powers. DB:05/25/2003 *)
    mSoln = 
      mSoln //.
        { 
          a : {(_Rule) ..} :> 
              Sequence[] /; 
                Or @@ (! IntegerQ[ #[[2]] ]& /@ a ),
          a : {(_Rule) ..} :> 
              Sequence[] /; 
                Or @@ ( #[[2]] < 0 & /@ a )
        };
     If[systemCleanUpDebug,
       Print[
         "If it is a system, we remove negative and non-integer solutions:"
       ];
       Print[CleanUpFunction[ mSoln ]];
     ];

    (* Removes Tracking Variables. *)
    eqnList = eqnList0 /. myTrackingVariable[_]:>1;

    If[systemCleanUpDebug,
      Print["eqnList, sans tracking variables is:"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Forms chiList. *)
    eqnList /. \[Chi][i_] :> 
      ( chiList = Append[chiList, \[Chi][i] ]; 1 );
    chiList = Union[chiList];

    If[systemCleanUpDebug,
      Print["chiList, the list of chi s are:"];
      Print[CleanUpFunction[chiList]];
    ];

    (* Finds constraints on chi. *)
    eqnList = 
      (
        Plus @@ Coefficient[(eqnList /. #),
                  F^Max[mList /. mSoln]
                ]& /@ mSoln
      ) /. (p_ -> q_) :> (p -> Factor[q]);

    If[systemCleanUpDebug,
      Print["mSoln, Checking in eqnList:"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Returns the good solutions. *)
    Return[mSoln];

  ]; (* end of module mSolve`SystemCleanUp *)


(* ::Subsubsection::Closed:: *)
(* (5h ) : procedure : mSolve`FixFreeM*)


(* Taken from Painleve Test code DB:05/15/2004. *)
mSolve`FixFreeM[
    mSoln_List,
    myMList_List,
    opts___?OptionQ
  ] :=
  Module[{ fixFreeMDebug = (* Debugging Boolean flag *)
            (mSolverVerbose /. {opts} /. Options[PDESpecialSolutions]), 
           mSoln0,
           mFree, 
           mFreeValues, mFixedValues,
           mValues
         }, (* Protected Local Variables *)
    
    (* Remove symbolic solutions, based on the code in SystemCleanUp. *)
    (* DB:07/29/2004 added removal of rational solutions. *)
    mSoln0 = 
      ( {Rest /@ (# /. Rule -> List), #}& /@ mSoln ) /. 
          {a_List, {(_Rule)..}} :> Sequence[] /;
            Not[ And @@ (FreeQ[ a, #] & /@ myMList  ) ];
    mSoln0 = mSoln0 /. 
      {a_List, {(_Rule)..}} :> Sequence[] /; 
        Not[ And @@ FreeQ[ a, Rational] ];
    mSoln0 = #[[2]]& /@ mSoln0;

    (* Warn the user when potential solutions are removed. *)
    If[Length[Complement[Union[Sort /@ mSoln], mSoln0] ] > 0,
      StylePrint[
        "The potential solutions "<>
        ToString[ 
          InputForm[
            CleanUpFunction[
              Complement[Union[Sort /@ mSoln], mSoln0] 
            ] 
          ]
        ] <> 
        " are being removed because they are under determined.  ", 
        "Message"
      ];
    ];

    If[fixFreeMDebug,
      Print["mSoln, after the underdetermined systems are removed:"];
      Print[CleanUpFunction[mSoln0]];
    ];

    (* Pick out the solutions with freedom. *)
    mFree = 
      Select[mSoln0, Length[#] < Length[myMList]&];

    If[fixFreeMDebug,
      Print["The dominant behaviors with one or more free \!\(M\_i\):"];
      Print[CleanUpFunction[ mFree ]];
    ];

    If[Length[mFree] >= 1,

      Message[PDESpecialSolutions`dominantBehavior::freevalues,
        CleanUpFunction[ mFree ]
      ];

      (* Substitutes in the values that are fixed, leaving the free values. *)
      mFreeValues = 
        (myMList /. #)& /@ mFree;
      mFixedValues = 
        (myMList /. #)& /@
          Complement[mSoln0, mFree];

      (* DB:02/08/2004 *)
      If[Length[mFixedValues] === 0,
        Message[PDESpecialSolutions`dominantBehavior::underdetermined];
        mFixedValues = 
          mFreeValues /. 
            m[_] :> 0
      ];

      If[fixFreeMDebug,
        Print["The free m values are:"];
        Print[CleanUpFunction[ mFreeValues ]];
        Print["The fixed m values are:"];
        Print[CleanUpFunction[ mFixedValues ]];
      ];

      mValues = 
        Transpose[
          { #,
            Sequence @@
            Cases[
              mFixedValues,
              # /. (m[i_] :> _)
            ]
          }
        ]& /@ mFreeValues;

      If[fixFreeMDebug,
        Print["The fixed values divided by free values:"];
        Print[CleanUpFunction[ mValues ]];
      ];

      mValues = 
        Sequence @@
          Thread[
            If[Head[First[#]] === Integer,
              First[#],
              Range[ MinDegreeOfThePolynomial /. {opts} 
                  /. Options[PDESpecialSolutions],
                  Max[Rest[#]]
              ]
            ]& /@ #
          ]& /@ mValues;

      If[fixFreeMDebug,
        Print["Fixing the free values from the " <>
          "MinDegreeOfThePolynomial up to max:"];
        Print[CleanUpFunction[ mValues ]];
      ];

      mValues = 
        ( Rule @@ #& /@ 
          Transpose[
            { myMList,
              #
            }
          ]
        )& /@ mValues;

      If[fixFreeMDebug,
        Print["The fixed values reformatted:"];
        Print[CleanUpFunction[ mValues ]];
      ];

      Return[ mValues ];

    ];

    Return[mSoln0];

  ]; (* end of module mSolve`FixFreeM *)


(* ::Subsubsection::Closed:: *)
(* (5i ) : procedure : mSolve`GenerateAlternativeSolutions*)


(* Finds free solutions that result from inequalities. *)
(* Added direct from old code DB:11/20/2002. *)
mSolve`GenerateAlternativeSolutions[
    mList_List, 
    opts___? OptionQ
  ]:=
  Module[{ n (* The number of alpha[i] *)
         }, (* Protected Local Variables *)
    
    n = Length[ mList ];

    Return[
      Thread[
        mList -> #
      ] & /@ 
        Flatten[
          Outer[
            List,
            Sequence @@ 
              Table[
                Range[ 
                  ( MinDegreeOfThePolynomial /. {opts} /. 
                    Options[PDESpecialSolutions] ),
                  ( MaxDegreeOfThePolynomial  /. {opts} /. 
                    Options[PDESpecialSolutions] )
                ],
                {n}
              ]
          ], 
          n - 1
        ]
    ]
  ]; (* end module mSolve`GenerateAlternativeSolutions *)


(* ::Subsubsection::Closed:: *)
(* (6 ) : procedure : PDESpecialSolutionsBuildSystem*)


(* ************************************************************************ *)
(* : Title : PDESpecialSolutionsBuildSystem.
*  : Author : Douglas Baldwin
*  : Date : 05/24/2001 *)
(* : Update : 01/12/2003 by Douglas Baldwin
*    Added debug statements and highest order equation solving.
*    Changes marked with DB:Date *)
(* : Update : 01/21/2003 by Douglas Baldwin
*    Added StripNonZero to the equations before they are sent to the solver.
*    This is mainly for printing the simplest system to the user, because 
*    AnalyzeAndSolve already strips the non-zeros. *)

PDESpecialSolutionsBuildSystem[mSoln_List, system_List, 
  vars_List, parameters_List, opts___?OptionQ]:=
  Block[{buildSystemDebug = False,
         Form,
         numberOfEquations,
         sqrtRules,
         funcRules,
         uRules,
         pureuRules,
         tempuRules,
         newSystem,
         waveparameters,
         param,
         unknowns,
         nonzeros,
         maxF,
         highestOrderSystem,
         highestOrderSolutions,
         myTemp,
         time = TimeUsed[]}, (* Protects Local Variables. *)

    (* Sets the form from the options. *)
    Form = 
      ToExpression[
        ToLowerCase[
          ToString[Form /. {opts} /. Options[PDESpecialSolutions]]
        ]
      ] /. {jacobisn->sn, jacobicn->cn};

    (* Sets a local variable to the number of equations given by user. *)
    numberOfEquations = Length[system];

    (* Sets up the way in which the system will be divided up *)
    (* in the next step, based on the Options set by the user. *)
    sqrtRules = 
      {tanh -> 0, 
       sech -> 0, 
       sechtanh -> 1-S^2,
       cn -> 0,
       sn -> 0
      };

    (* Sets up a list of rules for replacing the form to F. *)
    funcRules = {tanh -> T, sech -> S, sechtanh -> S, cn -> CN, sn -> SN};

    (* Converts the results of mSolve to an expression in T *)
    uRules =  (# /.
      (m[i_]->j_) :>
        (u[i][Form /. funcRules] -> 
          Evaluate[
            Sum[a[i,kk]*(Form /. funcRules)^kk, 
              {kk, 0, Numerator[j]}
            ]^(Sign[j] / Denominator[j]) + 
            If[(Form /. sqrtRules) =!= 0,
              Sqrt[Form /. sqrtRules]*
                Sum[b[i,kk]*(Form /. funcRules)^kk, 
                  {kk, 0, n[i] /. Flatten[#]}
              ],
              0
            ]
          ] (* closes evaluate *)
        )
       )& /@ mSoln;

    If[buildSystemDebug,
      Print["Before conversion in pure functions, these are the uRules : "];
      Print[CleanUpFunction[ uRules ]];
    ];

    (* WH:12/19/2001 modification: introduced tempuRules *)
    If[Verbose /. {opts} /. Options[PDESpecialSolutions],
      Print["Seeking polynomial solutions of the form"];
       tempuRules = DeleteCases[uRules,
            n[_]->_,
            2];
      Print[CleanUpFunction[tempuRules]];
    ];

    (* Prints out a warning, if it's taking a long time. *)
    If[TimeUsed[]-time>3,
      Print["Still building the nonlinear algebraic system, please wait."]
    ];

    (* Converts form of solutions given by solver to a pure *)
    (* function. *)
    toPure = 
      (# /. (a__[var__]->temp__) :> (a:>Function[{var}, temp]))&;

(* WH:01/23/2009 added the following line to see the format of pureuRules *)
    pureuRules = toPure[#]& /@ uRules;

    If[buildSystemDebug,
      Print["After conversion into pure function rules, the pureuRules are: "];
      Print[CleanUpFunction[ pureuRules ]];
    ];

    (* Applies the expressions in T to the system and removes the *)
    (* tracking variables by setting these to 1 *)
    newSystem = 
      Expand[
        system //. Append[toPure[#], myTrackingVariable[_]->1]
      ]& /@ uRules;

    If[buildSystemDebug,
      Print["Apply the expressions in T to the system gives: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Clears the denominator to simplify the system. *)
    newSystem = 
      Map[Together[#*Denominator[Together[#]]]&, newSystem, 2];

    If[buildSystemDebug,
      Print["Clearing the denominator, we get: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Creates a list with the wave parameters (c[1], c[2], ...) to be *)
    (* passed to the solver. DB:02/04/2003 Put mod with param instead *)
    (* of c_is.*)
    waveparameters = 
        Table[c[i], {i, Length[vars]}];

    (* DB:02/04/2003 Including mod with parameters. *)
    param = 
      Join[parameters,
        If[Form === cn || Form === sn, {mod}, {}]
      ];
    (* Creates a list of all the a[i,j]'s to be passed to the solver. *)
    unknowns =
      Table[
        {Table[a[i,j], {j, 0, Numerator[m[i] /. #]}],
          If[(n[i] /. # /. n[_]->0) > 0,
            Table[b[i,j], {j, 0, n[i] /. # /. n[_]->0}],
            Null
          ]}, 
        {i, numberOfEquations}]& /@ mSoln;

    unknowns = 
      DeleteCases[Sequence @@ #& /@ #& /@ unknowns, Null, Infinity];

    (* Creates a list of those variables which must be nonzero, so as *)
    (* to simplify the work of the solver. *)
    (* DB:01/12/2003 Commented out the Form =!= cn and sn. *)
    nonzeros = 
      Join[param, 
        If[Form =!= sechtanh (* && Form =!= cn && Form =!= sn *), 
          Last /@ #, 
          {}
        ], 
        waveparameters
      ]& /@ unknowns;

    (* Flattens the sublists and reorders them to speed up the solver. *)
    unknowns = 
    Map[
        Reverse,
           #[[2]]& /@ #& /@ 
           (Sort[{# /. a_[b_,c_]:>{c,a,b},#}& /@ Flatten[#] ]& /@ unknowns) 
       ];

    If[buildSystemDebug,
      Print["The unknowns, nonzeros and wave parameters are: "];
      Print[CleanUpFunction[{unknowns, nonzeros, waveparameters} ]];
    ];

    (* Expands the system. *)
    newSystem = newSystem /. (p_ -> q_) :> (p -> Expand[q]);

    (* Determines the maximum value of F in each of the cases. *)
    maxF = 
      Map[
        Exponent[#, 
          Form /. funcRules
        ]&, 
        newSystem
      ] /. -Infinity -> 0 (* DB:03/21/2003 Infinity rule added. *);

    If[buildSystemDebug,
      Print["The dominate power in each expression of new system is: "];
      Print[CleanUpFunction[ maxF ]];
    ];

    (* UnsortedUnion from Mathematica Book -- added DB:01/11/2003. *)
    (* Removed on Tuesday, January 14, 2003 DB:01/23/2003 *)
    (*
    UnsortedUnion[x_] := Module[{f}, f[y_] := (f[y] = Sequence[]; y); f /@ x];
    *)

    (* If the HigestOrderFirst option is set, then: *)
    If[HighestOrderFirst /. {opts} /. Options[PDESpecialSolutions],
      (* Creates a list of the highest order system. *)
      (* Rewritten by DB:01/14/2003 *)
      highestOrderSystem = 
        (# == 0)& /@ 
          MapThread[Coefficient[#1, Form /. funcRules, #2] &, 
            {#, Exponent[#, Form /. funcRules]}]& /@ newSystem;
      
      If[buildSystemDebug,
        Print["The highest order equations are: "];
        Print[CleanUpFunction[ highestOrderSystem ]];
      ];

      (* DB:01/21/2003 Strips the non-zeros at this step. *)
      highestOrderSystem = 
        MapThread[StripNonZero, {highestOrderSystem, nonzeros} ];

      If[buildSystemDebug,
        Print["Removes non-zeros from the system."];
        Print[CleanUpFunction[ highestOrderSystem ]];
      ];

      (* DB:01/12/2003 highestOrderSytem is then formatted to *)
      (* input into AnalyzeAndSolve *)
      highestOrderSystem = 
          Transpose[
            {highestOrderSystem, 
              unknowns, 
              Table[waveparameters, {Length[newSystem]}],
              Table[param, {Length[newSystem]}],
              nonzeros
            }
          ] /. (p_ -> q_) :> (p -> Factor[q]);

      If[buildSystemDebug,
        Print["The highest order system formatted for AnalyzeAndSolve: "];
        Print[CleanUpFunction[ highestOrderSystem ]];
      ];

      (* DB:01/12/2003 Find the solutions using AnalyzeAndSolve *)
      highestOrderSolutions = 
        Algebra`AnalyzeAndSolve`AnalyzeAndSolve @@ #& /@ 
          highestOrderSystem;

      If[buildSystemDebug,
        Print["The highest order equations' solutions are: "];
        Print[CleanUpFunction[ highestOrderSolutions ]];
      ];
    ];

    (* Sets up the way in which the system will be divided up *)
    (* in the next step, based on the Options set by the user. *)
    sqrtRules = 
      {tanh -> Null, 
       sech -> 1-S^2, 
       sechtanh -> 1-S^2,
       cn -> 1-mod-CN^2+2*mod*CN^2-mod*CN^4, 
       sn -> 1-SN^2-mod*SN^2+mod*SN^4
      };

    (* DB:02/28/2005 Added new Coefficient function, for 5.0 compatibility. *)
    myCoefficient[p_Plus, q_, 0] := Plus @@ Select[p, FreeQ[#,q]&]; 
    myCoefficient[p_, q_, 0] := Plus @@ Select[{p}, FreeQ[#,q]&]; 
    myCoefficient[p_Plus, q_, 1] := Plus @@ Cases[p, z_. q -> z]; 
    myCoefficient[p_, q_, 1] := Plus @@ Cases[{p}, z_. q -> z]; 

    (* Breaks up system into most general form. *)
    newSystem = 
      Flatten[
       {myCoefficient[#,Sqrt[Form /. sqrtRules],0]& /@ #, 
        myCoefficient[#,Sqrt[Form /. sqrtRules],1]& /@ #}
      ]& /@ #& /@ newSystem;

    If[buildSystemDebug,
      Print["After breaking the system up into {P,Q} (where P + Sqrt[]*Q): "];
      Print[CleanUpFunction[ newSystem ]];
    ];
    
    (* Brakes the expressions up newSystem by powers of T. *)
    (* Modified version by DB:01/11/2003 *)
    newSystem = 
      Table[
        Table[
          Union[
              DeleteCases[
                Flatten[
                  Table[
                    Table[
                      Coefficient[
                        Expand[newSystem[[case,k]] ], 
                        Form /. funcRules, 
                        i
                      ], 
                      {i, 0, maxF[[case,j]]}], 
                    {j, Length[maxF[[case]] ]}
                  ]
                ], 0
              ]
          ], {k, Length[newSystem[[case]] ]}
        ], {case, Length[newSystem]}
      ];

    If[buildSystemDebug,
      Print["The system after being broken up is: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Converts from expressions to equations. *)
    newSystem = 
      DeleteCases[(# == 0)& /@ Flatten[#]& /@ newSystem,
        False || True, Infinity];

    If[buildSystemDebug,
      Print["After flattening and removing all True or False items:"];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* DB:01/21/2003, Strips the non-zeros at this step. *)
    newSystem = 
      MapThread[StripNonZero, {newSystem, nonzeros} ];

    If[buildSystemDebug,
      Print["Removes non-zeros from the system."];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Prints out a warning if it's taking too long. *)
    If[
   (TimeUsed[]-time>3) && !(Verbose /. {opts} /. Options[PDESpecialSolutions]),
      Print["Still building the nonlinear algebraic system, please wait."]
    ];

    If[HighestOrderFirst /. {opts} /. Options[PDESpecialSolutions],
      (* DB:11/13/2002 Version to work with highest order solutions *)
      (* Combines into lists containing {newSystem, unknowns, *)
      (* waveparameters, param, nonzeros} for the solver. *)
      newSystem =
       ( 
         (* Expands the cases over the solutions for the highest terms *)
         (Sequence @@ 
            ( { (* Added Flattens on 11/13/02 to compensate *)
                (* for the output of highestOrderSolutions  *)
                (* StripNonZero added DB:02/02/2003. *)
               StripNonZero[
                 Flatten[(First[#] /. Last[#]) /. True -> Sequence[] ],
                 #[[-2]]
               ], 
               Sequence @@ Drop[Rest[#],-1],
               Flatten[Last[#]]
              }& /@ Thread[#, List, -1]
            )
         ) & /@ 
         (* Groups the information in the same form as the input *)
         (* to the solver. *)
           Transpose[
            {newSystem, 
              unknowns, 
              Table[waveparameters, {Length[newSystem]}],
              Table[param, {Length[newSystem]}],
              nonzeros,
              highestOrderSolutions
            }
          ]
        ) /. (p_ -> q_) :> (p -> Factor[q]),
      (* Combines into lists containing {newSystem, unknowns, *)
      (* waveparameters, param, nonzeros} for the solver. *)
      newSystem = 
        ( 
          Transpose[
            {newSystem, 
              unknowns, 
              Table[waveparameters, {Length[newSystem]}],
              Table[param, {Length[newSystem]}],
              nonzeros
            }
          ]
        ) /. (p_ -> q_) :> (p -> Factor[q]);
    ];

    If[buildSystemDebug,
      Print["The system formatted for AnalyzeAndSolve: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* DB:03/21/2003 Allows mSoln to be updated in main. *)
    newSystem = Thread[{mSoln, newSystem}];
    If[buildSystemDebug,
      Print["Threading mSoln"];
      Print[CleanUpFunction[ newSystem]];
    ];

    (* DB:03/21/2003 Remove inconsistant systems. *)
    newSystem = 
      newSystem /. { {_,{{___, False, ___}, __}} :> Sequence[], 
        {_,{{}, __}} :> Sequence[] };

    If[buildSystemDebug,
      Print["Removes inconsistant systems:  "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* If there are no systems to be solved, then abort. *)
    (* DB:03/21/2003 *)
    If[Length[newSystem] === 0,
      Message[ PDESpecialSolutionsBuildSystem::fail ];
      Abort[ ]
    ];

    (* DB:03/21/2003 Transpose added after threading mSoln above. *)
    Return[
      Transpose[newSystem]
    ];
  ]; (* end of block PDESpecialSolutionsBuildSystem *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (7 ) : procedure : PDESpecialSolutionsBuildSolutions*)


(* : Title : PDESpecialSolutionsBuildSolutions. *)
(* : Author : Douglas Baldwin *)
(* : Summary : Builds (includes massive simplification) *)
(*   and test the final solutions. *)

PDESpecialSolutionsBuildSolutions[solution_, mSoln_, eqns_, funcs_, vars_, 
  param_, opts___?OptionQ] :=
  Block[{NumericDebug = False, (* Debug for numeric tester. *)
         Form, (* Form defined by user. *)
         solutionRules, (* Local version of solution *)
         sqrtRules, (* Set by options. *)
         funcRules, (* Also set by options. *)
         uRules, (* Rules for creating the solutions. *)
         mySimplificationRules, (* Simplification rules. *)
         numericTestSolutions, (* tests validity of solutions in *)
                               (* numerical test. *)
         symbolicTestSolutions, (* tests the validity of solutions. *)
                                (* in symbolic test. *)
         newSymbolicTestSolutions, (* used in evaluation of expresssions *)
                                   (* with roots of cubics, quartics, etc. *)  
         evalNewSymbolicTestSolutions, (* ibid. *)
         mySymbol, (* ibid. *)
         variousRoots, (* ibid. *)
         ruleForMySymbol, (* ibid. *)
         rulesForMySymbols, (* ibid. *)
         tempSymbolicTestSolutions, (* used to control simplifications with *)
                                    (* simplify function *) 
         solns = {}, (* confirmed solutions. *)
         warn = {}, (* Collects a list of warnings due to simplification. *)
         time = TimeUsed[] (* A timer for length warnings. *)
        }, (* Protected Local Variables. *)

    (* Sets the form from the options. *)

    Form = 
      ToExpression[
        ToLowerCase[
          ToString[Form /. {opts} /. Options[PDESpecialSolutions]]
        ]
      ] /. {jacobisn -> sn, jacobicn -> cn};

    (* Sets up a local version to modify *)
    solutionRules = solution /. (p_ -> q_) :> (p -> Factor[q]); 

    (* Rules for building the solutions. *)
    sqrtRules = 
      {tanh -> 0, 
       sech -> 0, 
       sechtanh -> 
         1-Sech[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}] + phase]^2,
       cn -> 0,
       sn -> 0
      };
    funcRules = 
      {tanh -> 
         Tanh[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase], 
       sech -> 
         Sech[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase], 
       sechtanh -> 
         Sech[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase],
       cn -> 
         CN[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase,mod],
       sn -> 
         SN[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase,mod]
      };

    (* Converts the results of mSolve to an expression in T *)
    uRules =  
      (m[i_]->j_) :>
        (funcs[[i]] -> 
            Sum[a[i,kk]*(Form /. funcRules)^kk, 
              {kk, 0, Numerator[j]}
            ]^(1/Denominator[j]) + 
            Sqrt[Form /. sqrtRules]*
              Sum[b[i,kk]*(Form /. funcRules)^kk, 
                {kk, 0, n[i] /. Flatten[#]}
              ] 
        )&;

    (* Builds the solutions from the above rules and *)
    (* the powers of F listed in the passed mSoln. *)
    solutionRules = 
      DeleteCases[
        DeleteCases[
          Table[
            Table[
              Join[(mSoln[[jj]] /. uRules[mSoln[[jj]] ]) //. 
                  solutionRules[[jj, ii]],
                (# -> (# /. solutionRules[[jj,ii]]))& /@
                If[Form === cn || Form === sn, 
                  Append[param, mod], 
                  param
                ]
              ],
              {ii, Length[solutionRules[[jj]]]}
            ],
            {jj, Length[mSoln]}
          ],
          n[_]->_,
          Infinity
        ],
        Rule[a_, b_] /; a == b && FreeQ[a, Alternatives @@ funcs],
        Infinity
      ];

    (* Simplification rules for reducing the solution *)
    (* even further . . . so as to find more general  *)
    (* solutions. *)
    mySimplificationRules = 
      { Sqrt[xxx__^2] :> 
          (warn = Append[warn, "Sqrt[a^2]->a"]; xxx), 
        Sqrt[Power[yyy__,2]] :> 
          (warn = Append[warn, "Sqrt[a^2]->a"]; yyy), 
        Sqrt[-zzz__^2] :> 
          (warn = Append[warn, "Sqrt[-a^2]->I*a"]; I*zzz),
        Sqrt[-ttt_*zzz__^2] :> 
          (warn = Append[warn, "Sqrt[-a*b^2]->I*b*Sqrt[a]"];
           I*zzz*Sqrt[ttt]), 
(* WH:09/24/2019 tried to add this rule to test a sech or Sech solution *)
(* did not work !!! *)
(*
        Sech[xx__] :> 
        (warn = Append[warn, "Sech[x]->Sqrt[1 - Tanh[x]^2]"]; 
        Sqrt[1 - Tanh[xx]^2]) /; (Form === sech || Form === Sech), 
*)
(* WH:01/05/2010 the patterns on left may not be recognized *)
        (1-Sech[xx__]^2) -> Tanh[xx]^2,
        (1-Tanh[xx__]^2) -> Sech[xx]^2, 
(* begin replacement, both below created an infinite loop *)
(* Tanh[xx__]^2 -> 1-Sech[xx]^2, *)
(*        Sech[xx__]^2 -> 1-Tanh[xx]^2, *)
(* end replacement *)
(* WH:09/24/2019 added also Cn in addition to cn, Sn in addition to sn everywhere below *)
        JacobiDN[xx__, mm__]^2 :> 1-mm+mm*JacobiCN[xx,mm]^2 /; (Form === cn || Form === Cn),
        JacobiSN[xx__, mm__]^2 :> 1-JacobiCN[xx,mm]^2 /; (Form === cn || Form === Cn),
        JacobiDN[xx__, mm__] :> 
   (warn = Append[warn,"JacobiDN[x,mod] -> Sqrt[1-mod+mod*JacobiCN[x,mod]^2]"];
           Sqrt[1-mm+mm*JacobiCN[xx,mm]^2]
          ) /; (Form === cn || Form === Cn),
        JacobiSN[xx__, mm__] :> 
   (warn = Append[warn,"JacobiSN[x,mod] -> Sqrt[1-JacobiCN[x,mod]^2]"];
           Sqrt[1-JacobiCN[xx,mm]^2]
          ) /; (Form === cn || Form === Cn),
        JacobiDN[xx__, mm__]^2 :> 1-mm*JacobiSN[xx,mm]^2 /; (Form === sn || Form === Sn),
        JacobiCN[xx__, mm__]^2 :> 1-JacobiSN[xx,mm]^2 /; (Form === sn || Form === Sn),
        JacobiDN[xx__, mm__] :> 
          (warn = Append[warn,
                    "JacobiDN[x,mod]->Sqrt[1-mod*JacobiSN[x,mod]^2]"
                  ];
           Sqrt[1-mm*JacobiSN[xx,mm]^2]
          ) /; (Form === sn || Form === Sn),
        JacobiCN[xx__, mm__] :> 
          (warn = Append[warn, 
                    "JacobiSN[x,mod]->Sqrt[1-JacobiSN[x,mod]^2]"
                  ]; 
                  Sqrt[1-JacobiSN[xx,mm]^2]
          ) /; (Form === sn || Form === Sn)
      };
 
    (* Applies the above rules to the solutions. *)
    solutionRules = 
      FixedPoint[
        ((
          (( 
            # //. mySimplificationRules
          ) /. (p_ -> q_) :> (p -> Factor[q])) //. mySimplificationRules
        ) /. (p_ -> q_) :> (p -> Expand[q]))&,
        solutionRules,
        3
      ];

    (* DB:03/21/2003 Removes zero solutions. *)
    solutionRules = 
      solutionRules /. {___,_-> 0,___} :> Sequence[];
    
    (* Removes constant solutions *)
    solutionRules =
      Select[#, 
        !(And @@ (FreeQ[# /. (a_->b__):>b, Alternatives @@ vars]& /@ #))&
      ]& /@ solutionRules;

    If[Verbose /. {opts} /. Options[PDESpecialSolutions],
      Print["The possible non-trivial solutions (before any testing) are: "];
      Print[
        CleanUpFunction[
          ( 
            solutionRules /. {CN -> JacobiCN, SN -> JacobiSN} 
          ) /. (p_ -> q_) :> (p -> Factor[q])
        ]
      ];
    ];

    (* Prints out a warning, if it's taking a long time. *)
    If[TimeUsed[]-time>3,
      Print["Still building the exact solutions, please wait."]
    ];

    (* WH:03/17/2010 formatted the cellprint lines were too long, *)
    (* or print too small in Mathematica v. 7.0 *)
    (* Depending on the NumericTest option, it either tests the *)
    (* solutions numerically, or it doesn't. *)
    (* start if 0 *)
    If[ ( !(NumericTest /. {opts} /. Options[PDESpecialSolutions]) &&
          !(SymbolicTest /. {opts} /. Options[PDESpecialSolutions]) ),
      CellPrint[
        Cell[
        "These solutions are not being tested numerically or symbolically",
        "Message"
        ]
      ];
      CellPrint[
        Cell[
        "To test the solutions set either the NumericTest option to True ", 
        "Message"
        ]
      ];
      CellPrint[
        Cell[
        "or set the SymbolicTest option to True, or both. ", 
        "Message"
        ]
      ];
      (* WH:03/17/2010 formatted the cellprint lines were too long, *)
      (* or print too small in Mathematica v. 7.0 *)
      If[Length[warn]>0,
        CellPrint[
          Cell[
          "The following simplification rules are being used:",
          "Message"
          ] 
        ];
        CellPrint[
          Cell[
          ToString[Union[warn]],
          "Message"
          ] 
        ];
      ]; (* end if *)
      Return[
        Map[Union,
          (
            (
              solutionRules /. {CN -> JacobiCN, SN -> JacobiSN}
            ) /. (p_ -> q_) :> (p -> Expand[q])
          ) /. (p_ -> q_) :> (p -> Factor[q]), 2
        ]
      ]
    ]; (* end if 0 *)

    (* Converts form of solutions given by solver to a pure function. *)
    toPure = 
      (# /. (a__[var__]->temp__):> (a:>Function[{var}, temp]))&;

(* WH:01/23/2009 these tests can be removed later *)
(* 
Print["At xxxxxxx0, this is NumericTest :"];
Print[NumericTest];

Print["At xxxxxxx1, this is opts :"];
Print[opts];

Print["At xxxxxxx2, this is Options[PDESpecialSolutions] :"];
Print[Options[PDESpecialSolutions]];

Print["At xxxxxxx3, this is Verbose :"];
Print[Verbose];

Print["At xxxxxxx4, this is "<>
       "NumericTest /. {opts} /. Options[PDESpecialSolutions] :"];
Print[NumericTest /. {opts} /. Options[PDESpecialSolutions]];

Print["At xxxxxxx5, this is "<>
       "!(Verbose /. {opts} /. Options[PDESpecialSolutions]): "];
Print[!(Verbose /. {opts} /. Options[PDESpecialSolutions])];
*)

(* WH:01/23/2009 always print the message about numerically testing *)
    (* If statement for the numerically test option. *)
    If[NumericTest /. {opts} /. Options[PDESpecialSolutions],
      (* Sends message to user. *)
      If[(Verbose /. {opts} /. Options[PDESpecialSolutions]),
        Print["Numerically testing the solutions."]
      ];

(* was:
      If[!(VerboseTest /. {opts} /. Options[PDESolve]),
        Print["Numerically test the solutions."]
      ];
*)

(* WH:01/04/2010 Added a print statement *)
(* WH:03/17/2010 solutionRules enters numerical test *)

    If[VerboseTest,
       Print["The following solutions will be numerically tested:"];
       Print[CleanUpFunction[solutionRules]]
       ];

(* WH:03/17/2010 does this change format to a list of double lists? *)
(* code Baldwin: *)

      (* Tests numerically to make sure the above solutions are valid. *)
      numericTestSolutions =
        {(eqns /. a__ == b__:>a-b) /. 
          toPure[(# /. (p_ -> q_) :> (p -> TrigToExp[q]))], #}& /@ 
          #& /@ solutionRules;

(* WH:03/17/2010 *)
(*
Print["At Pt. R1, numericTestSolutions: "];
Print[CleanUpFunction[numericTestSolutions]];
*)

      randomVarRules = 
        Append[
          (# -> Random[Real, {-1, 1}])& /@ 
            Join[vars, Array[c, Length[vars]]],
          phase -> 0
        ];

      randomAijRules = 
        { a[_,_]->Random[Real, {-1, 1}], 
          b[_,_]->Random[Real, {-1, 1}], 
          Sequence @@ ((# -> Random[Real, {-1, 1}])& /@ 
              If[Form === cn || Form === sn, 
                Join[param, {mod}], 
                param
              ] 
            )
        };

      (* Numerically tests the solutions by replacing all the symbols with *)
      (* random numbers. *)
      numericTestSolutions = 
       { Or[
           And @@
           (
             Abs[ # ] < 10^(-$MachinePrecision/2)& /@ 
               ( ((
                   #[[1]] /. randomVarRules
                 ) /. (p_ -> q_) :> (p -> Expand[q])) /. 
                 randomAijRules /. 
                 {CN -> JacobiCN, SN-> JacobiSN}
               )
           ),
           And @@
           (
             Abs[ # ] < 10^(-$MachinePrecision/2)& /@ 
               ( ((
                   #[[1]] /. ( randomVarRules /. (a_ -> b_) :> (a -> -b) )
                 ) /. (p_ -> q_) :> (p -> Expand[q])) /. 
                 ( randomAijRules /. (a_ -> b_) :> (a -> -b) ) /. 
                 {CN -> JacobiCN, SN-> JacobiSN}
               )
           )
         ],
         #
       }& /@ #& /@ numericTestSolutions;

(* WH:03/17/2010 *)
(*
Print["At Pt. R2, numericTestSolutions: "];
Print[CleanUpFunction[numericTestSolutions]];
*)

      (* If it works for any of the trials, it keeps the solution. *)
      solns = 
        numericTestSolutions /. { {True, a_} :> a[[2]], 
                                  {False, _} :> Sequence[] };

(* WH:03/17/2010 *)
(*
Print["At Pt. R3, solns: "];
Print[CleanUpFunction[solns]];
Print["The above soln are the solutions that PASSED the NUMERICAL test"];
*)

(* WH:01/04/2010 Added a print statement *)
    If[VerboseTest,
       Print["The following solutions passed the numerical test:"];
       Print[CleanUpFunction[solns]]
       ];

(* WH:03/17/2010 *)
(*
Print["At Pt. R3-bis, solutionRules: "];
Print[CleanUpFunction[solutionRules]];
*)

(* WH:03/17/2010 change the lists solns and solutionRules artifically *)
(* to test if complement works *)

(* solns = solns /. { 15 -> N[Pi,4] }; *)

(* 
Print["At Pt. R3-tris, solns in raw form: "];
Print[solns];
*)
(*
Print["At Pt. R3-quatro (after modification), solns: "];
Print[CleanUpFunction[solns]];
Print["length of solns (after modification):", 
       Length[solns[[1]]]];
*)

(* solutionRules = solutionRules /. { 15 -> N[Pi,6] }; *)

(*
Print["At Pt. R3-5, solutionRules in raw form: "];
Print[solutionRules];
*)
(*
Print["At Pt. R3-6 (after modification), solutionRules: "];
Print[CleanUpFunction[solutionRules]];
Print["length of solutionRules (after modification):", 
       Length[solutionRules[[1]]]];
*)

(* Print["Now take complement of solutionRules and solns"]; *)

(* WH:03/17/2010 the complement below malfunctioned *)
(* Baldwin's code was: *)
(*
      numericTestSolutions = Complement[solutionRules, solns];
*)
(* WH:03/17/2010 replaced by *)

      numericTestSolutions = 
        { Complement[solutionRules[[1]], solns[[1]]] };

(* WH:03/17/2010 *)
(*
Print["At Pt. R4, coming from taking the complement, numericTestSolutions: "];
Print[CleanUpFunction[numericTestSolutions]];
Print["length of numericTestSolutions:", Length[numericTestSolutions[[1]]]];
*)
(* 
Print["The above numericTestSolution are the solutions that DID NOT PASS "<>
      " the NUMERICAL test"];
*)

(* WH:03/17/2010 formatted the cellprint lines were too long, *)
(* or print too small in Mathematica v. 7.0 *)
      If[(Map[Union, numericTestSolutions, 3] //.  {{}}->{}) != {},
        CellPrint[
          Cell[
          "After subsitution of the solutions into the PDE, the resulting "<>
          "expressions did not simplify to be less than 10^(" <>
          ToString[-$MachinePrecision/2] <>
          ") ",
          "Message"
          ]
        ];
        CellPrint[
          Cell[
          "when random numbers in [-1,1] were substituted for the " <>
          "unknowns.  " <>
          "This could be caused from Mathematica's assumption that " <>
          "Sqrt[a^2] -> a when a is numeric.  ",
          "Message"
          ]
        ];
        CellPrint[
          Cell[
          "Please test the corresponding solutions by hand or interactively "<>
          "with Mathematica.",
          "Message"
          ]
        ];
        Print[CleanUpFunction[#]]& 
          /@ numericTestSolutions;
      ];
      
    ]; (* End of numeric test if statement. *)

(* WH:01/23/2009 these tests can be removed later *)
(* 
Print["At yyyyyyy0, this is NumericTest :"];
Print[NumericTest];

Print["At yyyyyyy1, this is opts :"];
Print[opts];

Print["At yyyyyyy2, this is Options[PDESpecialSolutions] :"];
Print[Options[PDESpecialSolutions]];

Print["At yyyyyyy3, this is Verbose :"];
Print[Verbose];

Print["At yyyyyyy4, this is "<>
       "NumericTest /. {opts} /. Options[PDESpecialSolutions] :"];
Print[NumericTest /. {opts} /. Options[PDESpecialSolutions]];

Print["At yyyyyyy5, this is "<>
       "!(Verbose /. {opts} /. Options[PDESpecialSolutions]): "];
Print[!(Verbose /. {opts} /. Options[PDESpecialSolutions])];
*)

(* WH:01/23/2009 always print the message about symbolic testing *)
    (* The second testing If statement. *)
    If[SymbolicTest /. {opts} /. Options[PDESpecialSolutions],
      (* Sends message to user. *)
       If[(Verbose /. {opts} /. Options[PDESpecialSolutions]),
         Print["Symbolically testing the solutions."]
       ];

(* was: 
      If[!(VerboseTest /. {opts} /. Options[PDESolve]),
        Print["Symbolically test the solutions."]
      ];
*)

(* WH:01/04/2010 Added a line of code and a print statement. *)
(* Under the default setting, solns would come out of the numeric test. *)
(* therefore, the solns would be {} if numeric test is set to False. *)
(* So, if numeric test is false, set solns = solutionRules, but simplify *)
(* solutionRules a bit *)

       If[!(NumericTest /. {opts} /. Options[PDESpecialSolutions]), 
           solns = ( ( solutionRules /. {CN -> JacobiCN, SN -> JacobiSN}
           ) /. (p_ -> q_) :> (p -> Expand[q])
           ) /. (p_ -> q_) :> (p -> Factor[q])
       ];

(* WH:03/17/2010 only test solutions (soln) that passed the numeric test. *)
(* Added a print statement to specify which solutions are being tested. *)
      If[VerboseTest,
         If[(NumericTest /. {opts} /. Options[DDESpecialSolutions]), 
           Print["Only the solutions that passed the numeric test will "<>
                 "be tested symbolically."];
           Print["To test all solutions, set the option NumericTest to False."]
        ]
      ];
      If[VerboseTest,
         Print["The following solutions will be tested symbolically:"];
         Print[CleanUpFunction[solns]]
      ];

(* WH:03/17/2007 artificially mess up one of the solutions to test if the *)
(* code handles that correctly *)

(* solutionRules = solutionRules /. { 15 -> N[Pi,6] }; *)

(*
Print["At Pt. U1 (after modification), solutionRules: "];
Print[CleanUpFunction[solutionRules]];
Print["length of solutionRules (after modification):", 
       Length[solutionRules[[1]]]];
*)

(* WH:03/17/2010 only test the solutions solns that passed the numeric test *) 
(* if the numeric test was skipped then solns = solutionRules *)

      (* This sets up the input for the next block of code. *)
      (* In that, it takes the equation given by the user, *)
      (* and replaces the user defined functions (e.g. u[x,t]) *)
      (* with the functions found with the algorithm.  To replace *)
      (* the partial derivatives correctly, we must first convert *)
      (* the solutions to pure functions. *)

(* WH:03/17/2010 replaced solutionRules by solns *)

      symbolicTestSolutions =
        {(eqns /. a__ == b__:>a-b) /. 
          toPure[(# /. (p_ -> q_) :> (p -> TrigToExp[q]))], #}& /@ 
          #& /@ ( (* solutionRules *) 
                  solns /. {CN -> JacobiCN, SN-> JacobiSN});

(* WH:03/17/2010, check for format changes! *)
(* 
Print["At Pt. U2, solutionRules: "];
Print[CleanUpFunction[solutionRules]];
*)
      (* Attempts to simplify the expressions as much as possible. *)
      (* WH:01/05/2010 works fine on cases without roots of cubics, etc. *)

      symbolicTestSolutions = 
        ExpToTrig[
          FixedPoint[ 
            (( 
              (# /. (p_ -> q_) :> (p -> Expand[q])) /. mySimplificationRules
            ) /. (p_ -> q_) :> (p -> Factor[q])) /. 
            mySimplificationRules &, #, 10]&
            /@ symbolicTestSolutions
        ];
        (* WH:09/24/2019 apply one extra rule if Sech is present, then reverse the rule *)
        (* WH:03/30/2020 added a PowerExpand sinc Sqrt[(expression)^2] did not simplify into expression *)
        (* All to avoid having to use the slow FullSimplify function *)
        (* Print["At pt XXXXXXX1, symbolicTestSolutions = ", CleanUpFunction[symbolicTestSolutions]]; *)
        If[!FreeQ[CleanUpFunction[symbolicTestSolutions], Sech], 
           symbolicTestSolutions = PowerExpand[Factor[symbolicTestSolutions /. {Sech[xx__]->Sqrt[1-Tanh[xx]^2]}]];
          (* Print["At pt XXXXXXX2, symbolicTestSolutions = ", CleanUpFunction[symbolicTestSolutions]]; *)
           symbolicTestSolutions = PowerExpand[Expand[symbolicTestSolutions /. {Tanh[xx__]->Sqrt[1-Sech[xx]^2]}]]
          (* ; *)
          (* Print["At pt XXXXXXX3, symbolicTestSolutions = ", CleanUpFunction[symbolicTestSolutions]] *)
          ];
        
(* WH:03/17/2010 *)
(* 
Print["At Pt. U3, after applying FixedPoint, symbolicTestSolutions: "];
Print[CleanUpFunction[symbolicTestSolutions]];
Print["Check the format in comparison with solutionRules"];
*)

(* 
      Print["At Pt. B1, after fixedpoint algorithm, symbolicTestSolutions = "];
      Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
*)

(* WH:01/05/2010 added new piece of code to deal with expressions *)
(* involving unevaluated roots of cubics, quartics, etc. *)
(* start if 2 *)
      If[( Map[Union, symbolicTestSolutions,3] //. {{}}->{} ) != {} &&   
         ( FreeQ[symbolicTestSolutions, Root] === False ), 
          Print["Simplifying the remaining expressions (involving roots "<>
                "of cubics, quartics, etc.) "];
(*
          Print["At Pt. B2, symbolicTestSolutions = "];
          Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
*)
          newSymbolicTestSolutions = 
                symbolicTestSolutions /. { Root[a__,i_] -> mySymbol[i] };
(*
          Print["At Pt. B3, newSymbolicTestSolutions = "];
          Print[CleanUpFunction[#]]& /@ newSymbolicTestSolutions;
*)
          variousRoots = 
             Union[Cases[symbolicTestSolutions, Root[a__,i_],Infinity]];
(* 
          Print["At Pt. B4, variousRoots = "];
          Print[CleanUpFunction[#]]& /@ variousRoots;
*)
          ruleForMySymbol[i_] := 
                       { mySymbol[i] -> Part[variousRoots,i] };
(*
          Print["At Pt. B5, ruleForMySymbol[i] = "];
          Print[CleanUpFunction[ruleForMySymbol[i]]];
*)
          rulesForMySymbols = 
            Flatten[Table[ ruleForMySymbol[i],{i,1,Length[variousRoots]}]];
(*
          Print["At Pt. B6, rulesForMySymbols = "];
          Print[CleanUpFunction[#]]& /@ rulesForMySymbols;
*)
          evalNewSymbolicTestSolutions = 
               Map[Simplify,newSymbolicTestSolutions /. rulesForMySymbols];
(*
          Print["At Pt. B7, evalNewSymbolicTestSolutions = "];
          Print[CleanUpFunction[#]]& /@ evalNewSymbolicTestSolutions;
*)
          symbolicTestSolutions= evalNewSymbolicTestSolutions;
(*
          Print["At Pt. B9, symbolicTestSolutions = "];
          Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
*)

      ]; (* end if 2 *)

(* WH:01/05/2010 reluctantly added a simplify because expressions *)
(* involving sech did not fully simplify *)

        tempSymbolicTestSolutions = 
         DeleteCases[
           DeleteCases[symbolicTestSolutions,
             {{(0)..}, _List},
             Infinity
           ],
           {}
         ];
(*
        Print["At Pt. C1, tempSymbolicTestSolutions = "];
        Print[CleanUpFunction[#]]& /@ tempSymbolicTestSolutions;
*)

   If[tempSymbolicTestSolutions != {}, 
      symbolicTestSolutions = Map[Simplify, symbolicTestSolutions];

(*
      Print["At Pt. C4, after mapping simplify, symbolicTestSolutions = "];
      Print[CleanUpFunction[#]]& /@ symbolicTestSolutions
*)
      ];

(* for debugging only *)
(*
        If[( Map[Union, symbolicTestSolutions,3] //. {{}}->{} ) != {}, 
           result = Map[Union, symbolicTestSolutions,3] //. {{}}->{};
           Print["At Pt. C2, test for not equal to {}, result  ="];
           Print[CleanUpFunction[#]]& /@ result;
           symbolicTestSolutions = Map[Simplify, symbolicTestSolutions];
           Print["At Pt. C3, after mapping simplify, symbolicTestSolutions ="];
           Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
           ];

*)

(* for old code January 23, 2009  WH:01/05/2010 *) 
(* 
Print["At Pt. 1, before joining the symbolically tested solutions, solns = "];
Print[CleanUpFunction[solns]];
*)

(* WH:01/05/2010 do no longer join the original (not-tested) and the tested *)
(* solutions. *)
(*
      (* Pulls off the solutions which simplify to zero, and adds *)
      (* them to solns (the final output applies the union, so *)
      (* duplicate solutions are not an issue at this point). *)
      solns = 
        Join[solns,
          Cases[symbolicTestSolutions,
            {{(0)..}, _List},
            Infinity
          ] //. {{(0)..}, a_List}:>{a}
        ];
*)
(* by the following *)

(*
      solns = 
          Cases[symbolicTestSolutions,
            {{(0)..}, _List},
            Infinity
          ] //. {{(0)..}, a_List} :> {a} ;
*)

(* WH:03/17/2010 if a_List -> {a} *)
(* 
Print["At Pt. U4, if a_List -> {a}, then solns: "];
Print[CleanUpFunction[solns]];
*)

(* WH:03/17/2010 change a_List -> {a}, into a_List -> a *)

      solns = 
          Cases[symbolicTestSolutions,
            {{(0)..}, _List},
            Infinity
          ] //. {{(0)..}, a_List} :> a ;

(* WH:03/17/2010 *)
(* 
Print["At Pt. U5, if a_List -> a, then solns: "];
Print[CleanUpFunction[solns]];
Print["At Pt. U6, continue with this format for the rest of the computations"];
*)

(* in former code of January 23, 2009 WH:01/05/2010 *)
(*
Print["At Pt. 2, after joining the symbolically tested solutions, solns = "];
Print[CleanUpFunction[solns]];
*)

    If[VerboseTest,
       Print["The following solutions (in factored form) passed "<>
             "the symbolic test:"];
       Print[CleanUpFunction[solns]]
       ];

(* WH:01/05/2010 *)
(* in former code of January 23, 2009, applying a Union here did not work *)
(* 
Print["At Pt. 3, after applying a Union, solns = "];
Print[CleanUpFunction[solns]];
*)

      (* Removes all the good cases, so we may output the bad *)
      (* ones to the user. *)
(*
      Print["At Pt. A1, before deleting good cases, symbolicTestSolutions = "];
      Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
*)

      symbolicTestSolutions = 
        DeleteCases[
          DeleteCases[symbolicTestSolutions,
            {{(0)..}, _List},
            Infinity
          ],
          {}
        ];

(*
      Print["At Pt. A2, after deleting good cases, symbolicTestSolutions = "];
      Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
*)

      (* WH:03/17/2010 formatted the cellprint lines were too long, *)
      (* or print too small in Mathematica v. 7.0 *)
      (* start if 1 *)
      If[ ( Map[Union, symbolicTestSolutions,3] //. {{}}->{} ) != {},
        (* Sends out the left over (questionable) solutions to *)
        (* the user for hand inspection. *)
        CellPrint[
          Cell[
          "After substitution of the solution into the PDE,"<>
          " the resulting expressions did not simplify to zero. ",
          "Message"
          ]
        ];
         CellPrint[
          Cell[
          "Please test the corresponding solutions by hand or interactively "<>
          "with Mathematica.",
          "Message"
          ]
        ];
        Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
      ]; (* end if 1 *)
    ]; (* end if symbolic test *)

    (* WH:03/17/2010 formatted the cellprint lines were too long, *)
    (* or print too small in Mathematica v. 7.0 *)
    If[Length[warn]>0,
      CellPrint[
        Cell[
        "The following simplification rules are being used ",
        "Message"
        ]
      ];
      CellPrint[
        Cell[
        ToString[Union[warn]],
        "Message"
        ]
      ]
    ]; (* end if *)
    (* Returns the solution rules *)

(* 
Print["At Pt. 5, before applying the simplificatons, solns = "];
Print[CleanUpFunction[solns]];
*)

(* for debugging *) 
(* 
seeSolns = Union[
        (
          (
            solns /. {CN -> JacobiCN, SN -> JacobiSN}
          ) /. (p_ -> q_) :> (p -> Expand[q])
        ) /. (p_ -> q_) :> (p -> Factor[q])
      ];
*)

(* 
Print["At Pt. 6, after applying the simplificatons, returned are seeSolns = "];
Print[CleanUpFunction[seeSolns]];
*)

    Return[
      Union[
        (
          (
            solns /. {CN -> JacobiCN, SN-> JacobiSN}
          ) /. (p_ -> q_) :> (p -> Expand[q])
        ) /. (p_ -> q_) :> (p -> Factor[q])
      ]
    ];
]; (* end of block PDESpecialSolutionsBuildSolutions *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (8 ) : procedure : CleanUpFunction*)


(* : Title : CleanUpFunction *)
(* : Author : Douglas Baldwin *)
(* : Summary : Remove "PDESpecialSolutionsPrivate`" from output. *)

CleanUpFunction = 
  ToExpression[
    StringReplace[ToString[InputForm[#]],
      "Calculus`PDESpecialSolutions`Private`"->""
    ]
  ]& ;

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* 9 ) : Procedure : StripNonZero*)


(* : Title : StripNonZero *)
(* : Author : Douglas Baldwin *)
(* : Summary : Strips parameters from expressions. *)

StripNonZero[{a : (_List) ..}, param_List] := 
  StripNonZero[#, param] & /@ {a};

StripNonZero[theList_List, param_List] :=
    Module[
      {result, stripDebug = False}, (* Local Variables *)
     
      If[stripDebug,
        Print["The original expression is: "];
        Print[CleanUpFunction[ theList /. (p_ -> q_) :> (p -> Factor[q]) ]];
      ];

      (* Maps factor to every term, so as to have a constant base. *)
      result =  FactorList /@ (theList /. Equal[a_,b_]:>a-b);
      
      If[stripDebug,
        Print["The results of FactorList is: "];
        Print[CleanUpFunction[ result ]];
      ];
      
      If[stripDebug,
        Print["The rules are: "];
        Print[
          CleanUpFunction[ 
            {({#^_:1, _} :> Sequence[] & /@ param), 
             {_?NumericQ, _} :> Sequence[]
            } ]
        ];
      ];

      (* Remove terms that are non-zero. *)
      result = result /. ({#^_:1, _} :> Sequence[] & /@ param);

      (* Remove terms that are numeric. *)
      result = result /. {_?NumericQ, _} :> Sequence[];

      If[stripDebug,
        Print["The result after apply the non-zero rules: "];
        Print[CleanUpFunction[ result ]];
      ];
      
      (* Puts it back into standard form, {a, b} to a*b *)
      result = Times @@ (First[#]^Last[#]&) /@ #& /@ result;

      If[stripDebug,
        Print["Converting back to the standard form: "];
        Print[CleanUpFunction[ result ]];
      ];

      (* Converts expressions back into equations. *)
      If[! FreeQ[theList, Equal],
        result = Equal[#,0]& /@ result;
        ];

      If[stripDebug,
        Print["The final result of stripping the non-zeros is: "];
        Print[CleanUpFunction[ result ]];
      ];

      Return[ result ];

      ]; (* end of module StripNonZero *)


(* ::Section::Closed:: *)
(*End and EndPackage "PDESpecialSolutions" in Context`Private*)


End[]; (* `Private` context *)

Protect[PDESpecialSolutions];
SetAttributes[PDESpecialSolutions, ReadProtected];

EndPackage[];


(* ::Section::Closed:: *)
(* Begin package (old) "AnalyzeAndSolve" in Context`Private*)


(* ::Subsubsection::Closed:: *)
(* (1 ) : AnalyzeAndSolve*)


(* START OLD AnalyzeAndSolve *)
(* ************************************************************************ *)

(* Nonlinear algebraic solver by Unal Goktas (WRI) and Willy Hereman *)
(* written by Unal Goktas in October/November 2000 *)
(* Comments added by Douglas Baldwin on Monday, January 13, 2003 *)
(* DB:01/13/2003 *)

BeginPackage["Algebra`AnalyzeAndSolve`"];
Unprotect[AnalyzeAndSolve];

AnalyzeAndSolve::soln = "The solution `1` is being removed because it is inconsistent.";

Begin["`Private`"];

If[$VersionNumber < 4,
   Attributes[Internal`DeactivateMessages] = {HoldAll};
   Internal`DeactivateMessages[body_, msgs___MessageName] :=
      Module[{wasOn = Select[Hold[msgs], Head[#] =!= $Off &], result},
         CheckAbort[
            Scan[Off, wasOn];
            result = body;
            Scan[On, wasOn];
            result,
            Scan[On, wasOn];
            Abort[]
         ]
      ] (* end of module Internal`DeactivateMessages *)
]; (* end of if versionnumber < 4 *)

If[$VersionNumber >= 5,
  (* DB:01/08/2010 Added Version 7.0+ check. *)
  If[$VersionNumer >= 7,
     SetSystemOptions[
     "ReduceOptions" -> {"ReorderVariables" -> False}
     ],
     Developer`SetSystemOptions[
     "ReduceOptions" -> {"ReorderVariables" -> False}
     ]
  ]; (* end if versionnumber >= 7 *)
   myReduce[eqn_, vars_] :=
    LogicalExpand[
      Reduce[eqn, Reverse[vars]] /. Equal -> myEqual
    ] /. myEqual -> Equal,
   myReduce[eqn_, vars_] := Reduce[eqn, vars, Sort -> False]
]; (* end if versionnumber >= 5 *)


(* : Title : CleanUpFunction *)
(* : Author : Douglas Baldwin *)
(* : Summary : Remove "Algebra`AnalyzeAndSolve`Private`" from output. *)
(* : Added for debugging for AnalyzeAndSolve DB:01/14/2003 *)

CleanUpFunction = 
  ToExpression[
    StringReplace[ToString[InputForm[#]],
      { "Calculus`PDESpecialSolutions`Private`"->"",
        "Algebra`AnalyzeAndSolve`Private`"->""}
    ]
  ]& ;

(* This is the first call of AnalyzeAndSolve.  In this call, *)
(* The equations are converted into expressions equal to zero. *)
AnalyzeAndSolve[system: {HoldPattern[_ == _]..}, primaryunknowns_,
   secondaryunknowns_, parameters_, nonzeros_] :=
   AnalyzeAndSolve[(#[[1]]-#[[2]]&) /@ system, primaryunknowns,
      secondaryunknowns, parameters, nonzeros]

(* ************************************************************************ *)

(* Takes the newly recast version of AnalyzeAndSolve and converts its inputs *)
(* into a form readable by RecursivelyKeepTrack. *)
(* Warning: It is assumed that "system" is polynomial in "primaryunknowns", *)
(* "secondaryunknowns", and "parameters". *)
AnalyzeAndSolve[system_, primaryunknowns_, secondaryunknowns_, parameters_,
   nonzeros_] :=
   Block[{a, globalsol = {}, constraints},
      a = Together[({#}& /@ system) /. {{}}];
      constraints = (And @@ ((# != 0 &) /@ nonzeros));
      MapThread[
         RecursivelyKeepTrack[#1, #2, primaryunknowns, secondaryunknowns,
            parameters, nonzeros, constraints]&, {a, {{}}}];
      Union[globalsol]
   ]; (* end of block AnalyzeAndSolve *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (2 ) : procedure RecursivelyKeepTrack*)


(* Collects all the solutions at the end into globalsol. *)
(* Original code \[Ellipsis] replaced by the two following functions. *)

RecursivelyKeepTrack[{}, sol_, __] := (AppendTo[globalsol, sol]; {})

(* Terminates that recursive branch if the solution explodes or indeterminate. *)

RecursivelyKeepTrack[system_, sol_, __] /;
   (!FreeQ[system, DirectedInfinity] || !FreeQ[system, Indeterminate]) := {}
   
(* Main RecursivelyKeepTrack call.  It takes the system, cleans it up, sorts it by complexity level 
  (heuristic based on the degree of the polynomial and size of the expression), takes first equation 
  solves it, simplifies the solution and recursively calls it self on each unique branch of the solution. *)

RecursivelyKeepTrack[system_, sol_, primaryunknowns_, secondaryunknowns_,
   parameters_, nonzeros_, constraints_] :=
   Block[{a, b, c, recursiveDebug = False},
      (* Breaks the expression into a list and removes nonzeros and numbers. *)
      a = FactorListAndCleanUp[#, primaryunknowns, secondaryunknowns,
             parameters, nonzeros]& /@ system;
      (* Removes duplicates. Message added  DB:05/23/2003 *)
      a = 
        Union[a] /. {} :> 
        (Message[AnalyzeAndSolve::soln, CleanUpFunction[sol]];{});
      (* Sorts the system by the "ComplexityLevel" heuristic which is the *)
      (* degree of the polynomial*100 + LeafCount size of the expression. *)
      a = Sort[a, (ComplexityLevel[#1, primaryunknowns, secondaryunknowns,
                      parameters] <=
                   ComplexityLevel[#2, primaryunknowns, secondaryunknowns,
                      parameters]&)];
      (* DB:01/14/2003 Print statement added for debugging. *)
      If[recursiveDebug,
        Print["The order of the equations in AnalyzeAndSolve is: "];
        Print[
          CleanUpFunction[
            {ComplexityLevel[#1, primaryunknowns, secondaryunknowns,
                        parameters],#1}& /@ a
          ]
        ];
      ];
      (* Takes the first equation of the system of equations (which is the simplest according to the complexity heuristic) *)
      b = a[[1]];
      (* Then solves the first equation for only one variable. *)
      b = SolveStepByStep[#, primaryunknowns, secondaryunknowns, parameters,
                          constraints, sol]& /@ b;
      (* Flattens from the inside out:  {{{a,b},{c,d}}} -> {{a,b},{c,d}}. *)
      b = (Sequence @@ # &) /@ b;
      (* DB:02/04/2003 Added expand. *)
      b = b /. (p_ -> q_) :> (p -> Factor[q]);
      If[recursiveDebug,
        Print["The solution from the first equation is:"];
        Print[CleanUpFunction[ b ]];
      ];
      (* If there is no solution for the `simplest' equation, it terminates *)
      (* this recursive branch. *)
      If[Length[b] == 0, Return[{}]];
      (* Transposes the solution: {{a,b},{c,d}} -> {{a,c}, {b,d}} . *)
      b = Transpose[b];
      (* Adds constraints to the list, if there are any. .. && b && d *)
      c = (constraints && (And @@ #))& /@ b[[2]];
      (* Drops constraints. *)
      b = b[[1]];
      (* Applies the solution to the rest of the system and simplifies via *)
      (* a together and a numerator. *)
      a = Together[
             Internal`DeactivateMessages[Rest[a] /. b,
                Power::infy, General::indet
             ]
          ];
      a = Numerator[a];
      (* Removes any cases which it eliminates one of the other equations. *)
      a = DeleteCases[a, {___, 0, ___}, {2}];
      (* Takes the new solution, the one equation shorter system and the *)
      (* constraint and continues the recursive process. *)
      MapThread[
         RecursivelyKeepTrack[#1, #2, primaryunknowns, secondaryunknowns,
            parameters, nonzeros, #3]&, {a, b, c}]
   ]; (* end of block RecursivelyKeepTrack *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (3 ) : FactorListAndCleanUp*)


(* Performs a factor list and then removes from it any nonzeros or numbers. *)
(* Ex: -4 + 8a - 4b + 8ab - b^2 + 2ab^2 *)
(*    -> {{1, 1}, {-1 + 2*a, 1}, {2 + b, 2}} *)
(*     -> {{-1 + 2*a}, {2 + b}} *)
FactorListAndCleanUp[
   system_, primaryunknowns_, secondaryunknowns_, parameters_, nonzeros_] :=
   Block[{a = FactorList /@ system},
      (* DB:02/04/2003 Remove terms that are non-zero. *)
      a = a /. ({#^_:1, _} :> Sequence[] & /@ nonzeros);
      (* DB:02/04/2003 Remove terms that are numeric. *)
      a = a /. {_?NumericQ, _} :> Sequence[];
      a = Flatten[Map[First[#]&, a, {2}]];
      Union[a]
   ]; (* end of block FactorListAndCleanUp *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (4 ) : ComplexityLevel*)


(* New complexity analyzer by Douglas Baldwin DB:02/03/2003 *)

ComplexityLevel[expr_List, primaryunknowns_, secondaryunknowns_, parameters_]:=
  Max[
    ComplexityLevel[#,primaryunknowns,secondaryunknowns,parameters] & /@ expr
  ] 

ComplexityLevel[expr_,primaryUnknowns_,secondaryUnknowns_,parameters_]:=
  Module[
    { primaryComplexity = Select[primaryUnknowns, !FreeQ[expr,#]&],
      secondaryComplexity= Select[secondaryUnknowns, !FreeQ[expr,#]&],
      parameterComplexity= Select[parameters, !FreeQ[expr,#]&],
      exprLength = If[Head[Expand[expr]] === Plus, Length[Expand[expr]], 1],
      complexityDebug = False
     },
    
    primaryComplexity  = Exponent[expr, primaryComplexity] ; 
    secondaryComplexity = Exponent[expr, secondaryComplexity];
    parameterComplexity = Exponent[expr, parameterComplexity]; 

    If[complexityDebug,
      Print["The precept sequence for the complexity analyzer is: "];
      Print[
        CleanUpFunction[{primaryComplexity, secondaryComplexity, 
           parameterComplexity, exprLength}
        ]
      ];
    ];
    Return[
      Min @@ 
       Flatten[{1*primaryComplexity, 2*secondaryComplexity, 
         3*parameterComplexity}] + exprLength
    ];

  ]; (* end of module ComplexityLevel *)

(* WH:03/13/2010 put sets of parenthesis around (a) and (b) *)
(* ************************************************************************ *)

(* ::Subsubsection::Closed:: *)
(* (5 ) : SubComplexityLevel*)

(* This computes the leaves of the complexity analysis tree. The complexity heuristic (
   smaller is better) is either 
     (a) the exponent of the expression if it is polynomial, or 
     (b) 100*b*level + size of expression, where b is the number 
         of expressions which are of the level type (primary, secondary, 
         parameter) and the level: primary = 1, secondary = 2, param = 3 *)
         
SubComplexityLevel[expr_, a_, b_, level_] :=
   Block[{c = Select[a, PolynomialQ[expr, #]&]},
      Which[
         Length[c] == 0,
         100*b*level+LeafCount[expr],
         True,
         Min[Exponent[expr, c]]
      ]
   ]; (* end of block SubComplexityLevel *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (6 ) : SolveStepByStep*)


(* solves a single equation *)

(* Takes the factor terms which have the primary unknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with the secondary *)
(* unknowns, parameters, constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[primaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, 
          Flatten[{secondaryunknowns, parameters}],
          constraints, sol
       ]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep 1 *)

(* ************************************************************************ *)

(* Takes the factor terms which have the secondaryunknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with parameters,  *)
(* constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[secondaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, parameters, constraints, sol]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep 2 *)

(* ************************************************************************ *)

(* Takes the factor terms which have the parameters and pass it on to the *)
(* SubSolveStepByStep to be solved along with constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[parameters, q], -1]];
      (
       SubSolveStepByStep[eqn, a, {}, constraints, sol]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep 3 *)

(* ************************************************************************ *)

(* Takes anything that isn't composed of primary unknowns, secondary *)
(* unknowns, or parameters and returns an empty set. *)
SolveStepByStep[___] := {}

(* Takes the equation and primary unknowns (which are either THE primary unknowns, THE secondary unknowns, 
   or THE parameters from above).  
   1. If the equation is polynomial in any of the unknowns, it selects them and sorts them by power/exponent 
      and then includes the unknowns that the equation is not polynomial in.  If the equation is not polynomial 
      in any of the unknowns, it takes the order that they were given in.
   2. Uses Reduce to solve the equation (along with find the constraints).
   3. Then it converts the results to rules (same form as Solve) and returns an empty list if it is empty. 
   4. If there is a solution, it removes a != b type results from the form of the solution outputted by Reduce.
   5. It then applies the results of the solution to the rest of the solution.
   6. Formats the solution so that each sublist contains the latest solution branches along with the previous 
      solutions in a flattened and unique list. *)
      
SubSolveStepByStep[eqn_, primaryunknowns_, pars_, constraints_, sol_] :=
   Block[{a, b, c},
      a = Select[primaryunknowns, PolynomialQ[eqn, #]&];
      If[Length[a] != 0,
         a = Sort[a, Exponent[eqn, #1] <= Exponent[eqn, #2]&];
         a = Flatten[{a, Complement[primaryunknowns, a]}],
         a = primaryunknowns
      ];
      c = myReduce[eqn == 0 && constraints, Flatten[{a, pars}]];
      a = {ToRules[c]};
      If[Length[a] == 0, Return[{}]];
      c = Cases[{#}, p_ != q_, -1]& /@ If[Head[c] === Or, List @@ c, {c}];
      b = Internal`DeactivateMessages[sol /. a, Power::infy, General::indet];
      Union[Transpose[{Flatten /@ Thread[{b, a}, List, 2], c}]]
   ]; (* end of block SubSolveStepByStep *)

(* ************************************************************************ *)


(* ::Section::Closed:: *)
(*End and EndPackage (old) "AnalyzeAndSolve" in Context`Private*)


End[]; (* `Private` context *)
SetAttributes[AnalyzeAndSolve, ReadProtected];
EndPackage[];

(* END OLD AnalyzeAndSolve *)


(* ::Section::Closed:: *)
(* Begin package (new) "AnalyzeAndSolve" in Context`Private*)


(* ::Subsubsection::Closed:: *)
(* (1 ) : AnalyzeAndSolve*)


(* START NEW AnalyzeAndSolve *)

(* ************************************************************************ *)
(* : Title : AnalyzeAndSolveV2.m 
*  : Author : Douglas Baldwin, Unal Goktas, and Willy Hereman
*  : Email : solve@douglasbaldwin.com
*  : Date Modified : Thursday, March 4, 2010 by Douglas Baldwin
*  : History : First developed by Unal Goktas (WRI) and Willy Hereman and 
*    written by Unal Goktas in October/November 2000; 
*    comments added and complexity analyzer redesigned by Douglas Baldwin 
*    in February 2003; 
*    redesigned by DB in February 2007 to use depth-first search rather than 
*    a recursive breadth-first search; 
*    DB finished redesign in March 2010. *)

(* ************************************************************************ *)

BeginPackage["Algebra`AnalyzeAndSolve`"];
Unprotect[AnalyzeAndSolve];

AnalyzeAndSolve::soln = "The solultion `1` is being removed because it is inconsistent.";

Begin["`Private`"];

If[$VersionNumber < 4,
   Attributes[Internal`DeactivateMessages] = {HoldAll};
   Internal`DeactivateMessages[body_, msgs___MessageName] :=
      Module[{wasOn = Select[Hold[msgs], Head[#] =!= $Off &], result},
         CheckAbort[
            Scan[Off, wasOn];
            result = body;
            Scan[On, wasOn];
            result,
            Scan[On, wasOn];
            Abort[]
         ]
      ] (* end of module Internal`DeactivateMessages *)
]; (* end of if versionnumber < 4 *)

If[$VersionNumber >= 5,
	(* DB:1/8/2010 Added Version 7.0+ check. *)
	If[$VersionNumer >= 7,
		 SetSystemOptions[
			"ReduceOptions" -> {"ReorderVariables" -> False}
		 ],
		 Developer`SetSystemOptions[
			"ReduceOptions" -> {"ReorderVariables" -> False}
		 ]]; (* end if versionnumber >= 7 *)
   myReduce[eqn_, vars_] :=
    LogicalExpand[
      Reduce[eqn, Reverse[vars]] /. Equal -> myEqual
    ] /. myEqual -> Equal,
   myReduce[eqn_, vars_] := Reduce[eqn, vars, Sort -> False]
]; (* end if versionnumber >= 5 *)

(* ************************************************************************ *)


(* : Title : CleanUpFunction *)
(* : Author : Douglas Baldwin *)
(* : Summary : Remove "Algebra`AnalyzeAndSolve`Private`" from output. *)
(*    Added for debugging for AnalyzeAndSolve by DB:1/14/2003 *)

CleanUpFunction = 
  ToExpression[
    StringReplace[ToString[InputForm[#]],
      { "Calculus`PDESpecialSolutions`Private`"->"",
        "Calculus`DDESpecialSolutions`Private`"->"",
        "Algebra`AnalyzeAndSolve`Private`"->""}
    ]
  ]& ;

(* ************************************************************************ *)


(* : Title : AnalyzeAndSolve *)
(* : Author : Douglas Baldwin *)
(* : Summary : Takes a list of equations which depend on primary unknowns, 
*  secondary unknowns, and parameters and solves for the unknowns and 
*  parameters in an depth-first search which takes advantage of the given 
*  nonzero unknowns to simplify the expressions. *)

AnalyzeAndSolve[system_, primaryunknowns_, secondaryunknowns_, 
      parameters_, nonzeros_] :=
   Block[{  sys = system /. Equal[a_,b_]:>a-b, (* A local copy of system. *)
            constraints, (* Constraints on the possible solutions. *)
            theList, (* The search tree. *)
            soln = {}, (* The solution. *)
            currentSystem, (* The system of equations to be solved. *)
            currentSolutions, (* Expressions for known variables. *)
            currentSoln, (* The new solution from the simplest equation. *)
            currentConstraints, (* The constraints on future solutions. *)
            theNextNode, (* The next node to be expanded. *)
            depthFirstSolveDebug = False,
            recursiveDebug = False
         }, (* Protected local variables. *)
			sys = Numerator[Together[({#}& /@ sys)]];
      (* Takes the nonzeros given by the user and puts them in the form *)
      (* needed by Reduce. *)
      constraints = (And @@ ((# != 0 &) /@ nonzeros));

      (* The first node of the search tree. *)
      theList = {{{sys,{},constraints}}};

      While[True, (* Begin While A1 *)

         If[( !FreeQ[theList[[-1,1,1]], DirectedInfinity] || 
               !FreeQ[theList[[-1,1,1]], Indeterminate] || 
               !FreeQ[theList[[-1,1,1]], False] ),

               (* Goes back to the next branch. *)
               While[ Length[theList[[-1]]] === 1, 
                  theList = Drop[theList,-1]; 
                  (* If all branches have been searched, return soln. *)
                  If[ Length[theList] === 0, Return[soln] ];
               ];
               
               (* Removes the branch just solved for. *)
               theList = 
                  Append[Drop[theList,-1], Rest[theList[[-1]]]];

               If[depthFirstSolveDebug,
                 Print["The pruned search tree:"];
                 Print[CleanUpFunction[ theList ]];
               ];
         ];           

        
         If[theList[[-1,1,1]] === {}, (* Begin If A2 *)
(* * * * * * * * * * * * * *  If TRUE of If A2 * * * * * * * * * * * * * *  *)
               If[depthFirstSolveDebug,
                 Print["The current search tree is:"];
                 Print[CleanUpFunction[ theList ]];
               ];

               (* Adds new solution to soln. *)
               AppendTo[soln, theList[[-1,1,2]] ];

               If[depthFirstSolveDebug,
                 Print["The complete set of solutions is:"];
                 Print[CleanUpFunction[ soln ]];
               ];

               (* Goes back to the next branch. *)
               While[ Length[Last[theList]] === 1, 
                  theList = Drop[theList,-1]; 
                  (* If all branches have been searched, return soln. *)
                  If[ Length[theList] === 0, Return[soln] ];
               ];
               
               (* Removes the branch just solved for. *)
               theList =   
                  Append[Drop[theList,-1], Rest[theList[[-1]]]];

               If[depthFirstSolveDebug,
                 Print["The pruned search tree:"];
                 Print[CleanUpFunction[ theList ]];
               ],
(* * * * * * * * * * * * * *  If FALSE of If A2 * * * * * * * * * * * * * *  *)

               (* Applies the current solutions to the system. *)
               
               currentSystem = 
		 FactorListAndCleanUp[#, primaryunknowns, secondaryunknowns,
		       parameters, nonzeros]& /@ theList[[-1,1,1]];
               (* Pulls off the first solution of each list. *)
               currentSolutions = theList[[-1,1,2]];
               (* Pulls off the corresponding contraints on *)
               (* the above solutions. *)
               currentConstraints = theList[[-1,1,3]];

               If[depthFirstSolveDebug,
                 Print["The last entry in theList is:"];
                 Print[CleanUpFunction[ Last[theList] ]];
                 Print["The current system is:"];
                 Print[CleanUpFunction[ currentSystem ]];
                 Print["The current list of solutions is:"];
                 Print[CleanUpFunction[ currentSolutions ]];
                 Print["The current list of contraints is:"];
                 Print[CleanUpFunction[ currentConstraints ]];
               ];

               (* Removes duplicates. Message added DB:5/23/2003 *)
               currentSystem = 
                 Union[currentSystem] /. {} :> 
                 (Message[AnalyzeAndSolve::soln, 
                          CleanUpFunction[currentSolutions]];{});

               If[depthFirstSolveDebug,
                 Print["The system with duplicates removed is:"];
                 Print[CleanUpFunction[ currentSystem ]];
               ];

               (* Sorts the system by the "ComplexityLevel" heuristic. *)
               (* DB:3/2/2010 Changed back to Sort[List, Test]. *)
               currentSystem = 
                 Sort[currentSystem, 
                   (ComplexityLevel[#1, primaryunknowns, 
                        secondaryunknowns, parameters] <=
                      ComplexityLevel[#2, primaryunknowns, 
                          secondaryunknowns, parameters]&)];
               (* DB:1/14/2003 Print statement added for debugging. *)
               If[depthFirstSolveDebug || recursiveDebug,
                 Print["The order of the equations in AnalyzeAndSolve is: "];
                 Print[
                   CleanUpFunction[
                     {ComplexityLevel[#1, primaryunknowns, secondaryunknowns,
                                 parameters],#1}& /@ currentSystem
                   ]
                 ];
               ];
               
               (* Takes the first equation of the system of equations (which *)
               (* is the simplest according to the complexity heuristic) *)
               (* and then solves it for only one variable. *)
               currentSoln = 
                  SolveStepByStep[#, primaryunknowns, 
                     secondaryunknowns, parameters, currentConstraints, 
                     currentSolutions]& /@ currentSystem[[1]];
		     (* Flattens from the inside out:  
                        {{{a,b},{c,d}}} -> {{a,b},{c,d}}. *)
			currentSoln = (Sequence @@ # &) /@ currentSoln;
			currentSoln = 
                               currentSoln /. (p_ -> q_) :> (p -> Factor[q]);
			       If[depthFirstSolveDebug || recursiveDebug,
                 Print["The solution from the first equation is:"];
                 Print[CleanUpFunction[ currentSoln ]];
               ];

               (* If there is no solution for the `simplest' equation, *)
               (* it terminates this branch of the search tree. *)
               If[Length[currentSoln] == 0, (* Begin If A3 *)
(* * * * * * * * * * * * * *  If TRUE of If A3 * * * * * * * * * * * * * *  *)
                  (* Goes back to the next branch. *)
                  While[ Length[Last[theList]] === 1, 
                     theList = Drop[theList,-1]; 
                     (* If all branches have been searched, return soln. *)
                     If[ Length[theList] === 0, Return[soln] ];
                  ];
                  
                  theList =   
                    Append[Drop[theList,-1], Rest[theList[[-1]]]];

                  If[depthFirstSolveDebug,
                    Print["The pruned search tree:"];
                    Print[CleanUpFunction[ theList ]];
                  ],  
(* * * * * * * * * * * * * * If FALSE of If A3 * * * * * * * * * * * * * *  *)
                  (* Transposes the solution: 
                     {{a,b},{c,d}} -> {{a,c}, {b,d}} *)
                  currentSoln = Transpose[currentSoln];
                  (* Adds constraints to the list, if there are any. .. 
                                                   && b && d *)
                  currentConstraints = 
                     (currentConstraints && (And @@ #))& /@ currentSoln[[2]];
                  (* Drops constraints. *)
                  currentSoln = currentSoln[[1]];
                  (* Applies the solution to the rest of the system *)
                  (* and simplifies via a together and a numerator. *)
                  currentSystem = Together[
                         Internal`DeactivateMessages[
                            Rest[currentSystem] /. currentSoln,
                            Power::infy, General::indet
                         ]
                      ];
                  currentSystem = Numerator[currentSystem];

                  If[depthFirstSolveDebug,
                    Print["The current system is:"];
                    Print[CleanUpFunction[ currentSystem ]];
                  ];

                  (* Breaks the expression into a list and removes 
                                nonzeros and numbers. *)
                  currentSystem = Numerator[currentSystem];
                  (* If any of the equations are satisfied, remove them. *)
                  currentSystem = 
                         DeleteCases[currentSystem, {___, 0, ___}, {2}];

                  (* Reformat for the system and solutions to be passed 
                                                 as the next node. *)
                  theNextNode = 
                     MapThread[ {#1, #2, #3}&,
                           {currentSystem, currentSoln, currentConstraints}];
                  (* Remove any invalid solutions. *)
                  theNextNode = 
			DeleteCases[theNextNode, 
                        {a_List,_List,_And} /; 
                           (!FreeQ[a, DirectedInfinity] || 
                            !FreeQ[a, Indeterminate]),
                        {2}];

                  If[depthFirstSolveDebug,
                     Print["The current (cleaned up) system is:"];
                     Print[CleanUpFunction[ currentSystem ]];
                     Print["The theList argument being passed to the next 
                            depthFirstSolve is:"];
                     Print[CleanUpFunction[ Append[theList,theNextNode ] ]];
                  ];

                  (* Takes the new solution, the one equation shorter system 
                                             and the *)
                  (* constraint and continues to the next step lower node. *)
                  AppendTo[theList, theNextNode];
               ]; (* End If A3 *)
         ]; (* End If A2 *)
      ]; (* End While A1 *)
   ]

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (3 ) : FactorListAndCleanUp*)


(* Performs a factor list and then removes from it any nonzeros or numbers. *)
(* Ex: -4 + 8a - 4b + 8ab - b^2 + 2ab^2 *)
(*    -> {{1, 1}, {-1 + 2*a, 1}, {2 + b, 2}} *)
(*     -> {{-1 + 2*a}, {2 + b}} *)
FactorListAndCleanUp[
   system_, primaryunknowns_, secondaryunknowns_, parameters_, nonzeros_] :=
   Block[{a = FactorList /@ system},
      (* DB:2/4/2003 Remove terms that are non-zero. *)
      a = a /. ({#^_:1, _} :> Sequence[] & /@ nonzeros);
      (* DB:2/4/2003 Remove terms that are numeric. *)
      a = a /. {_?NumericQ, _} :> Sequence[];
      a = Flatten[Map[First[#]&, a, {2}]];
      Union[a]
   ]; (* end of block FactorListAndCleanUp *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (4 ) : ComplexityLevel*)


(* New complexity analyzer by Douglas Baldwin on DB:2/3/2003 *)
ComplexityLevel[expr_List, primaryunknowns_, secondaryunknowns_, parameters_]:=
  Max[
    ComplexityLevel[#,primaryunknowns,secondaryunknowns,parameters] & /@ expr
  ] 

ComplexityLevel[expr_,primaryUnknowns_,secondaryUnknowns_,parameters_]:=
  Module[
    { primaryComplexity = Select[primaryUnknowns, !FreeQ[expr,#]&],
      secondaryComplexity= Select[secondaryUnknowns, !FreeQ[expr,#]&],
      parameterComplexity= Select[parameters, !FreeQ[expr,#]&],
      exprLength = If[Head[Expand[expr]] === Plus, Length[Expand[expr]], 1],
      complexityDebug = False
     },
    
    primaryComplexity  = Exponent[expr, primaryComplexity] ; 
    secondaryComplexity = Exponent[expr, secondaryComplexity];
    parameterComplexity = Exponent[expr, parameterComplexity]; 

    If[complexityDebug,
      Print["The precept sequence for the complexity analyzer is: "];
      Print[
        CleanUpFunction[{primaryComplexity, secondaryComplexity, 
           parameterComplexity, exprLength}
        ]
      ];
    ];
    Return[
      Min @@ 
       Flatten[{1*primaryComplexity, 2*secondaryComplexity, 
         3*parameterComplexity}] + exprLength
    ];

  ]; (* end of module ComplexityLevel *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (5 ) : SubComplexityLevel*)


(* This computes the leaves of the complexity analysis tree. *)
(* The complexity heuristic (smaller is better) is either *)
(*   (a) the exponent of the expression if it is polynomial, or *)
(*   (b) 100*b*level + size of expression, where b is the number *)
(*      of expressions which are of the level type (primary, secondary, *)
(*      parameter), and the level: primary = 1, secondary = 2, param = 3 *)
SubComplexityLevel[expr_, a_, b_, level_] :=
   Block[{c = Select[a, PolynomialQ[expr, #]&]},
      Which[
         Length[c] == 0,
         100*b*level+LeafCount[expr],
         True,
         Min[Exponent[expr, c]]
      ]
   ]; (* end of block SubComplexityLevel *)

(* ************************************************************************ *)


(* ::Subsubsection::Closed:: *)
(* (6 ) : SolveStepByStep*)


(* solves a single equation *)

(* Takes the factor terms which have the primary unknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with the secondary *)
(* unknowns, parameters, constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[primaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, 
          Flatten[{secondaryunknowns, parameters}],
          constraints, sol
       ]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep 1 *)

(* ************************************************************************ *)

(* Takes the factor terms which have the secondaryunknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with parameters,  *)
(* constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[secondaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, parameters, constraints, sol]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep 2 *)

(* ************************************************************************ *)

(* Takes the factor terms which have the parameters and pass it on to the *)
(* SubSolveStepByStep to be solved along with constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[parameters, q], -1]];
      (
       SubSolveStepByStep[eqn, a, {}, constraints, sol]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep 3 *)

(* ************************************************************************ *)

(* Takes anything that isn't composed of primary unknowns, secondary unknowns, or parameters and returns an empty set. *)

SolveStepByStep[___] := {}

(* Takes the equation and primary unknowns (which are either THE primary *)
(* unknowns, THE secondary unknowns, or THE parameters from above).  *)
(* 1. If the equation is polynomial in any of the unknowns, it selects *)
(*    them and sorts them by power/exponent and then includes the unknowns *)
(*    that the equation is not polynomial in.  If the equation is not *)
(*    polynomial in any of the unknowns, it takes the order that they *)
(*    were given in.  *)
(* 2. Uses Reduce to solve the equation (along with find the constraints). *)
(* 3. Then it converts the results to rules (same form as Solve) and *)
(*    returns an empty list if it is empty. *)
(* 4. If there is a solution, it removes a != b type results from the *)
(*    form of the solution outputted by Reduce. *)
(* 5. It then applies the results of the solution to the rest of the *)
(*    solution. *)
(* 6. Formats the solution so that each sublist contains the latest solution *)
(*    branches along with the previous solutions in a flattened and unique *)
(*    list. *)

SubSolveStepByStep[eqn_, primaryunknowns_, pars_, constraints_, sol_] :=
   Block[{a, b, c},
      a = Select[primaryunknowns, PolynomialQ[eqn, #]&];
      If[Length[a] != 0,
         a = Sort[a, Exponent[eqn, #1] <= Exponent[eqn, #2]&];
         a = Flatten[{a, Complement[primaryunknowns, a]}],
         a = primaryunknowns
      ];
      c = myReduce[eqn == 0 && constraints, Flatten[{a, pars}]];
      a = {ToRules[c]};
      If[Length[a] == 0, Return[{}]];
      c = Cases[{#}, p_ != q_, -1]& /@ If[Head[c] === Or, List @@ c, {c}];
      b = Internal`DeactivateMessages[sol /. a, Power::infy, General::indet];
      Union[Transpose[{Flatten /@ Thread[{b, a}, List, 2], c}]]
   ]; (* end of block SubSolveStepByStep *)

(* ************************************************************************ *)


(* ::Section::Closed:: *)
(*End and EndPackage (new) "AnalyzeAndSolve" in Context`Private*)


End[]; (* `Private` context *)
SetAttributes[AnalyzeAndSolve, ReadProtected];
EndPackage[];
(* WH:03/30/2020 *)
Print["Built-in package AnalyzeAndSolveV2.m of March 13, 2010 was successfully loaded."];

(* END NEW AnalyzeAndSolve *)

(* ************************************************************************ *)

(* ::Section::Closed:: *)
(* Feedback when package is loaded *)

(* RK 13.03.2020 *)
(* WH:03/30/2020 did not work *)
(* mydate = Style[String[Part[Date[], 2], "-",Part[Date[], 3], "-",Part[Date[], 1]], Bold, 10, Blue]; *)
(* Print["Package ", Style["PDESpecialSolutionsV4-Mar30-2020-RK-WH.m",Bold,11,Blue],
      " from March 30, 2020 was successfully loaded on ", mydate /. {String -> Print}]; *)
(* date = print[Part[Date[], 2], "-", Part[Date[], 3], "-", Part[Date[], 1]]; *)

date = Date[ ][[1;;3]]//Reverse;
(* $print = " "; *)
(* 
print["On","Package ",Style["PDESpecialSolutionsV4-Mar30-2020-RK-WH.m",Bold,11,Blue],
      " from March 30, 2020 was successfully loaded on ",Style[date,Bold,10,Red]];
*)
(*
Print["Package ", Style["PDESpecialSolutionsV4-Mar30-2020-RK-WH.m",Bold,12,Blue],
      " from March 30, 2020 was successfully loaded on ", Style[date,Bold,12,Red]];
*)
Print["Package ", Style["PDESpecialSolutionsV4-Jul4-2020.m",Bold,12,Blue],
      " from July 4, 2020 was successfully loaded on ", Style[date,Bold,12,Red]];
Print["Based on Version 4, last updated on March 30, 2020 by Robert Kragler and Willy Hereman. \n",
      "Previously updated by Hereman on September 24, 2019. \n",
      "Based on Version 3, last updated by Hereman on March 21, 2010. \n",
      "Previously updated by Goktas on December 13, 2009 and by Hereman on January 8 and January 23, 2009. \n",
      "Based on code first released by Baldwin, Goktas, and Hereman on February 28, 2005."];

(* ************************************************************************ *)
