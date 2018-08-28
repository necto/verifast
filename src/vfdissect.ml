open Ast
open Lexer
open Parser
open Verifast0
open Verifast
open Arg
open Printf

let dump_context_to_file file ctxts termnode_to_string =
  let outfile = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  let last_exec = List.find (function | Executing _ -> true | _ -> false) ctxts in
  output_string outfile "\n--[another execution]--{\n";
  begin
    match last_exec with
    | (Executing (hp, env, _, str)) ->
      begin
        List.iter (fun (var,value) ->
            output_string outfile ("(" ^ var ^ " = " ^ (termnode_to_string value) ^ ")\n")) env;
        List.iter (function Chunk ((g, literal), targs, coef, ts, size) ->
            (* print_endline (string_of_chunk (Chunk ((g, literal), targs, coef, ts, size))); *)
            output_string outfile ("(" ^ (termnode_to_string g) ^ "(");
            output_string outfile (String.concat ", " (List.map termnode_to_string ts));
            output_string outfile "))\n";
          ) hp
      end
    | _ -> failwith " no exec "
  end ;
  List.iter (function
      | Assuming tn -> output_string outfile ("(" ^ (termnode_to_string tn) ^ ")\n")
      | _ -> ()) ctxts;
  output_string outfile "\n}\n";
  flush outfile;
  close_out outfile

(*
   free_vars contains the variable names that can be assigned in the e1 expression.
   assignments are the assignments the the variables imposed by the caller.
   assignments lhs must always be a subset of free_vars.
   assignments is add-only.
*)
let rec reducible_exprs verbose free_vars assignments e1 e2 =
  let pats_literal pats =
    List.for_all (function LitPat _ -> true | _ -> false ) pats
  in
  let get_lit_pat_exprs pats =
    pats |> List.map (function LitPat e -> e | _ -> failwith "non literal pattern")
  in
  let handle_pure_fun_call name1 name2 args1 args2 =
    if (not (String.equal name1 name2) ||
        List.length args1 != List.length args2) then
      None
    else
      List.fold_left2 (fun acc expr1 expr2 ->
          match acc with
          | Some assignments ->
            reducible_exprs verbose free_vars assignments expr1 expr2
          | None -> None)
        (Some assignments) args1 args2
  in
  let handle_call_with_pats name1 name2 pats1 pats2 =
    if (pats_literal pats1) && (pats_literal pats2) then
      handle_pure_fun_call
        name1 name2
        (get_lit_pat_exprs pats1)
        (get_lit_pat_exprs pats2)
    else None
  in
  match e1, e2 with
  | True _, True _ -> Some assignments
  | False _, False _ -> Some assignments
  | Null _, Null _ -> Some assignments
  | ExprAsn (_, e1), _ -> reducible_exprs verbose free_vars assignments e1 e2
  | _, ExprAsn (_, e2) -> reducible_exprs verbose free_vars assignments e1 e2
  | Var (_, name1), Var (loc, name2)
  | Var (_, name1), WVar (loc, name2, _)
  | WVar (_, name1, _), Var (loc, name2)
  | WVar (_, name1, _), WVar (loc, name2, _) ->
    if (List.mem name1 free_vars) then begin
      match List.assoc_opt name1 assignments with
      | None -> Some ((name1, Var (loc, name2))::assignments)
      | Some Var (_, x)
      | Some WVar (_, x, _) -> if String.equal x name2 then Some assignments else None
      | Some _ -> None
    end else if String.equal name1 name2 then Some assignments else None
  | WVar (loc, name1, _), _
  | Var (loc, name1), _ ->
    if (List.mem name1 free_vars) then begin
      match List.assoc_opt name1 assignments with
      | None -> Some ((name1, e2)::assignments)
      | Some _ -> None
    end else None (* TODO: allow the case when the assignment is the same value (ignoring loc) *)
  | Operation (_, op1, exprs1), Operation (_, op2, exprs2)
  | Operation (_, op1, exprs1), WOperation (_, op2, exprs2, _)
  | WOperation (_, op1, exprs1, _), Operation (_, op2, exprs2)
  | WOperation (_, op1, exprs1, _), WOperation (_, op2, exprs2, _) ->
    if (op1 != op2 || List.length exprs1 != List.length exprs2) then None
    else
      List.fold_left2 (fun acc expr1 expr2 ->
          match acc with
          | Some assignments ->
            reducible_exprs verbose free_vars assignments expr1 expr2
          | None -> None)
        (Some assignments) exprs1 exprs2
  | WPureFunCall (_, name1, _, args1),
    CallExpr (_, name2, _, _, args2, _) ->
    if pats_literal args2 then
      handle_pure_fun_call name1 name2 args1 (get_lit_pat_exprs args2)
    else None
  | CallExpr (_, name1, _, _, args1, _),
    WPureFunCall (_, name2, _, args2) ->
    if pats_literal args1 then
      handle_pure_fun_call name1 name2 (get_lit_pat_exprs args1) args2
    else None
  | WPureFunCall (_, name1, _, args1),
    WPureFunCall (_, name2, _, args2) ->
    handle_pure_fun_call name1 name2 args1 args2
  | PredAsn (_, predref1, _, _, pat_list1),
    PredAsn (_, predref2, _, _, pat_list2)
  | PredAsn (_, predref1, _, _, pat_list1),
    WPredAsn (_, predref2, _, _, _, pat_list2)
  | WPredAsn (_, predref1, _, _, _, pat_list1),
    PredAsn (_, predref2, _, _, pat_list2)
  | WPredAsn (_, predref1, _, _, _, pat_list1),
    WPredAsn (_, predref2, _, _, _, pat_list2) ->
    handle_call_with_pats predref1#name predref2#name pat_list1 pat_list2
  | CallExpr (_, name1, _, _, pat_list1, _),
    WPredAsn (_, predref2, _, _, _, pat_list2) ->
    handle_call_with_pats name1 predref2#name pat_list1 pat_list2
  | WPredAsn (_, predref1, _, _, _, pat_list1),
    CallExpr (_, name2, _, _, pat_list2, _) ->
    handle_call_with_pats predref1#name name2 pat_list1 pat_list2
  | CallExpr (_, name1, _, _, pat_list1, _),
    PredAsn (_, predref2, _, _, pat_list2) ->
    handle_call_with_pats name1 predref2#name pat_list1 pat_list2
  | PredAsn (_, predref1, _, _, pat_list1),
    CallExpr (_, name2, _, _, pat_list2, _) ->
    handle_call_with_pats predref1#name name2 pat_list1 pat_list2
  | _, _ ->
    if verbose then
      Printf.printf "mismatch %s ~~~ %s\n"
        (string_of_expr ~verbose:true e1)
        (string_of_expr ~verbose:true e2);
    None

let _ =
  let print_msg l msg =
    print_endline (string_of_loc l ^ ": " ^ msg)
  in
  let verify ?(emitter_callback = fun _ -> ()) (print_stats : bool) (options : options) (prover : string) (path : string)
      (breakpoint_lino : int option) (query : string option) (context_export_file : string option) (export_lino : int option) (emitHighlightedSourceFiles : bool) =
    let verify range_callback =
      let exit l =
        Java_frontend_bridge.unload();
        exit l
      in
      try
        let use_site_callback declKind declLoc useSiteLoc = () in
        let my_breakpoint = match breakpoint_lino with | Some lino -> Some (path,lino) | None -> None in
        let my_exportpoint =
          match export_lino with
          | Some lino ->
            let expfname = match context_export_file with
              | Some fname -> fname
              | None -> failwith "must supply also export file"
            in
            close_out (open_out expfname);
            Some ((
                object
                  method run: 'termnode. 'termnode context list ->
                    ('termnode -> string) -> unit =
                    dump_context_to_file expfname
                end),
                  path,lino)
          | None -> None
        in
        let lemmas : Verifast1.lemma_record list ref = ref [] in
        let register_lemma f =
          lemmas := f::!lemmas
        in
        let stats = verify_program ~emitter_callback:emitter_callback prover
            options path register_lemma range_callback use_site_callback (fun _ -> ())
            my_breakpoint my_exportpoint None in

        match query with
        | None -> printf "No query found.";
        | Some query -> begin
            printf "query %s supplied. Scanning lemmas\n" query;
            let qq = match parse_query ("requires true; ensures " ^ query) with
              | None -> failwith "malformed query"
              | Some (pre,post) -> post
            in
            printf "%d lemmas registered\n" (List.length !lemmas);
            printf "Deparsed query: %s\n" (string_of_expr qq);
            !lemmas |> List.iter (function {Verifast1.name=name;Verifast1.type_params;Verifast1.params;Verifast1.precond;Verifast1.postcond} ->
              match reducible_exprs false (List.map fst params) [] postcond qq with
              | Some assignments -> printf "MATCH: ";
                assignments |> List.iter (fun (lhs,rhs) ->
                    printf "%s = %s; " lhs (string_of_expr rhs););
                printf "\n";
                printf "%s<%s>(" name (String.concat "," type_params);
                params |> List.iter (fun (name, type_) ->
                    printf "%s %s, " (string_of_type type_) name;);
                printf ")\nrequires %s\n" (string_of_expr precond);
                printf "ensures %s\n" (string_of_expr postcond);
                printf "\n\n";
              | None -> ()
              );
          end;

          if print_stats then stats#printStats;
          print_endline ("0 errors found (" ^ (string_of_int (stats#getStmtExec)) ^ " statements verified)");
          Java_frontend_bridge.unload();
      with
        PreprocessorDivergence (l, msg) -> print_msg l msg; exit 1
      | ParseException (l, msg) -> print_msg l ("Parse error" ^ (if msg = "" then "." else ": " ^ msg)); exit 1
      | CompilationError(msg) -> print_endline (msg); exit 1
      | StaticError (l, msg, url) -> print_msg l msg; exit 1
      | SymbolicExecutionError (ctxts, l, msg, url) ->
        (*
        let _ = print_endline "Trace:" in
        let _ = List.iter (fun c -> print_endline (string_of_context c)) (List.rev ctxts) in
        let _ = print_endline ("Heap: " ^ string_of_heap h) in
        let _ = print_endline ("Env: " ^ string_of_env env) in
        *)
        let _ = print_msg l msg in
        exit 1
    in
    if emitHighlightedSourceFiles then
      begin
        let sourceFiles : (string * (((int * int) * (int * int)) * range_kind) list ref) list ref = ref [] in
        let range_callback kind ((path1, line1, col1), (path2, line2, col2)) =    
          assert (path1 = path2);
          let path = path1 in
          let ranges =
            if List.mem_assoc path !sourceFiles then
              List.assoc path !sourceFiles
            else
              begin
                let ranges : (((int * int) * (int * int)) * range_kind) list ref = ref [] in
                sourceFiles := (path, ranges)::!sourceFiles;
                ranges
              end
          in
          ranges := (((line1, col1), (line2, col2)), kind)::!ranges
        in
        verify range_callback;
        print_endline "Emitting highlighted source files...";
        let emit_source_file (path, ranges) =
          let text = readFile path in
          let n = String.length text in
          let outpath = path ^ ".html" in
          let outfile = open_out_bin outpath in
          output_string outfile "<html><head><title>";
          output_string outfile (Filename.basename path);
          output_string outfile "</title>";
          let stylesheet =
            "<style>\n\
             .keyword {color: blue; font-weight: bold}\n\
             .ghostKeyword {color: #DB9900; font-weight: bold}\n\
             .ghostRange {color: #CC6600}\n\
             .ghostRangeDelimiter {color: gray}\n\
             .comment {color: #008000}\n\
             .error {color: red; text-decoration: underline}\n\
             </style>"
          in
          output_string outfile stylesheet;
          output_string outfile "</head><body><pre>";
          let ranges = !ranges in
          let lexico cx cy (x1, y1) (x2, y2) = let dx = cx x1 x2 in if dx = 0 then cy y1 y2 else dx in
          let compare_pos = lexico compare compare in
          let compare_loc = lexico compare_pos (fun pos1 pos2 -> - compare_pos pos1 pos2) in
          let compare_start_pos (l1, kind1) (l2, kind2) = compare_loc l1 l2 in
          let ranges = List.sort compare_start_pos ranges in
          let rec emit_postfix offset line col inside_ranges before_ranges =
            match inside_ranges with
              ((line0, col0), kind)::inside_ranges when line0 = line && col0 = col ->
              output_string outfile "</span>";
              emit_postfix offset line col inside_ranges before_ranges
            | _ ->
              if offset = n then
                ()
              else
                match before_ranges with
                  (((line0, col0), pos1), kind)::before_ranges when line0 = line && col0 = col ->
                  output_string outfile "<span class=\"";
                  let kindClass =
                    match kind with
                      KeywordRange -> "keyword"
                    | GhostKeywordRange -> "ghostKeyword"
                    | GhostRange -> "ghostRange"
                    | GhostRangeDelimiter -> "ghostRangeDelimiter"
                    | CommentRange -> "comment"
                    | ErrorRange -> "error"
                  in
                  output_string outfile kindClass;
                  output_string outfile "\">";
                  begin
                    match inside_ranges with
                      (pos2, _)::_ when compare_pos pos2 pos1 < 0 -> let ((l1, c1), (l2, c2)) = (pos1, pos2) in Printf.printf "%s (%d, %d) < (%d, %d)" path l1 c1 l2 c2; assert false
                    | _ -> emit_postfix offset line col ((pos1, kind)::inside_ranges) before_ranges
                  end
                | _ ->
                  let c = text.[offset] in
                  if c = '\r' && offset + 1 < n && text.[offset + 1] = '\n' then
                    begin
                      output_string outfile "\r\n";
                      emit_postfix (offset + 2) (line + 1) 1 inside_ranges before_ranges
                    end
                  else if c = '\r' || c = '\n' then
                    begin
                      output_byte outfile (int_of_char c);
                      emit_postfix (offset + 1) (line + 1) 1 inside_ranges before_ranges
                    end
                  else
                    begin
                      if c = '<' || c = '&' then
                        output_string outfile (Printf.sprintf "&#%d;" (int_of_char c))
                      else
                        output_byte outfile (int_of_char c);
                      emit_postfix (offset + 1) line (col + 1) inside_ranges before_ranges
                    end
          in
          emit_postfix 0 1 1 [] ranges;
          output_string outfile "</pre></body></html>";
          close_out outfile;
          print_endline ("Emitted " ^ outpath)
        in
        List.iter emit_source_file !sourceFiles
      end
    else
      verify (fun _ _ -> ())
  in
  let stats = ref false in
  let verbose = ref 0 in
  let disable_overflow_check = ref false in
  let prover: string ref = ref default_prover in
  let compileOnly = ref false in
  let isLibrary = ref false in
  let allowAssume = ref false in
  let simplifyTerms = ref false in
  let allowShouldFail = ref false in
  let emitManifest = ref false in
  let emitDllManifest = ref false in
  let allModules: string list ref = ref [] in
  let dllManifestName = ref None in
  let emitHighlightedSourceFiles = ref false in
  let exports: string list ref = ref [] in
  let outputSExpressions : string option ref = ref None in
  let runtime: string option ref = ref None in
  let query: string option ref = ref None in
  let provides = ref [] in
  let breakpoint_lino : int option ref = ref None in
  let context_export_file : string option ref = ref None in
  let export_lino : int option ref = ref None in
  let keepProvideFiles = ref false in
  let include_paths: string list ref = ref [] in
  let define_macros: string list ref = ref [] in
  let library_paths: string list ref = ref ["CRT"] in
  let safe_mode = ref false in
  let header_whitelist: string list ref = ref [] in
  let linkShouldFail = ref false in
  let useJavaFrontend = ref false in
  let enforceAnnotations = ref false in
  let allowUndeclaredStructTypes = ref false in
  let dataModel = ref data_model_32bit in
  let vroots = ref [Util.crt_vroot Util.default_bindir] in
  let add_vroot vroot =
    let (root, expansion) = Util.split_around_char vroot '=' in
    let expansion = Util.abs_path expansion in
    if not (Sys.file_exists expansion) then
      failwith (Printf.sprintf "In definition of vroot '%s': bad expansion '%s': no such file" root expansion);
    if String.length root = 0 then
      failwith (Printf.sprintf "Bad root name '%s': should be nonempty" root);
    String.iter (function 'A'..'Z'|'_'|'0'..'9' -> () | _ -> failwith (Printf.sprintf "Bad root name '%s': should contain only uppercase letters, underscores, and digits" root)) root;
    begin match root.[0] with 'A'..'Z' -> () | _ -> failwith (Printf.sprintf "Bad root name '%s': should start with an uppercase letter" root) end;
    vroots := List.append (List.filter (fun (x, y) -> x <> root) !vroots) [(root, expansion)]
  in

  (* Explanations that are an empty string ("") become hidden in the
   * "--help" output. When adding options, you can consider writing an
   * explanation or just " " to prevent this, or document why the
   * new option should be hidden.
  *)
  let cla = [ "-stats", Set stats, " "
            ; "-verbose", Set_int verbose, "-1 = file processing; 1 = statement executions; 2 = produce/consume steps; 4 = prover queries."
            ; "-disable_overflow_check", Set disable_overflow_check, " "
            ; "-prover", String (fun str -> prover := str), "Set SMT prover (" ^ list_provers() ^ ")."
            ; "-c", Set compileOnly, "Compile only, do not perform link checking."
            ; "-shared", Set isLibrary, "The file is a library (i.e. no main function required)."
            ; "-allow_assume", Set allowAssume, "Allow assume(expr) annotations."
            ; "-runtime", String (fun path -> runtime := Some path), " "
            ; "-query", String (fun q -> query := Some q), " "
            ; "-allow_should_fail", Set allowShouldFail, "Allow '//~' annotations that specify the line should fail."
            ; "-emit_vfmanifest", Set emitManifest, " "
            ; "-emit_dll_vfmanifest", Set emitDllManifest, " "
            ; "-emit_dll_vfmanifest_as", String (fun str -> dllManifestName := Some str), " "
            ; "-bindir", String (fun str -> let p = Util.abs_path str in Util.set_bindir p; add_vroot ("CRT=" ^ p)), "Set custom bindir with standard library"
            ; "-vroot", String (fun str -> add_vroot str), "Add a virtual root for include paths and, creating or linking vfmanifest files (e.g. MYLIB=../../lib). Ill-formed roots are ignored."
            ; "-emit_highlighted_source_files", Set emitHighlightedSourceFiles, " "
            ; "-provides", String (fun path -> provides := !provides @ [path]), " "
            ; "-keep_provide_files", Set keepProvideFiles, " "
            ; "-breakpoint", Int (fun brp -> breakpoint_lino := Some brp), "Set the breakpoint line."
            ; "-context_export_file", String (fun f -> context_export_file := Some f), "File to store the logical context of the exportpoint."
            ; "-exportpoint", Int (fun ctp -> export_lino := Some ctp), "Set the line number for context dumps"
            ; "-emit_sexpr",
              String begin fun str ->
                outputSExpressions := Some str;
                SExpressionEmitter.unsupported_exception := false
              end,
              "Emits the AST as an s-expression to the specified file."
            ; "-emit_sexpr_fail",
              String begin fun str ->
                outputSExpressions := Some str;
                SExpressionEmitter.unsupported_exception := true
              end,
              "Emits the AST as an s-expression to the specified file; raises exception on unsupported constructs."
            ; "-export", String (fun str -> exports := str :: !exports), " "
            ; "-I", String (fun str -> include_paths := str :: !include_paths), "Add a directory to the list of directories to be searched for header files."
            ; "-D", String (fun str -> define_macros := str :: !define_macros), "Predefine name as a macro, with definition 1."
            ; "-L", String (fun str -> library_paths := str :: !library_paths), "Add a directory to the list of directories to be searched for manifest files during linking."
            ; "-safe_mode", Set safe_mode, "Safe mode (for use in CGI scripts)."
            ; "-allow_header", String (fun str -> header_whitelist := str::!header_whitelist), "Add the specified header to the whitelist."
            ; "-link_should_fail", Set linkShouldFail, "Specify that the linking phase is expected to fail."
            ; "-javac", Unit (fun _ -> (useJavaFrontend := true; Java_frontend_bridge.load ())), " "
            ; "-enforce_annotations", Unit (fun _ -> (enforceAnnotations := true)), " "
            ; "-allow_undeclared_struct_types", Unit (fun () -> (allowUndeclaredStructTypes := true)), " "
            ; "-target", String (fun s -> dataModel := data_model_of_string s), "Target platform of the program being verified. Determines the size of pointer and integer types. Supported targets: " ^ String.concat ", " (List.map fst data_models)
            ]
  in
  let process_file filename =
    if List.exists (Filename.check_suffix filename) [ ".c"; ".java"; ".scala"; ".jarsrc"; ".javaspec" ]
    then
      begin
        let options = {
          option_verbose = !verbose;
          option_disable_overflow_check = !disable_overflow_check;
          option_allow_should_fail = !allowShouldFail;
          option_emit_manifest = !emitManifest;
          option_vroots = !vroots;
          option_allow_assume = !allowAssume;
          option_simplify_terms = !simplifyTerms;
          option_runtime = !runtime;
          option_provides = !provides;
          option_keep_provide_files = !keepProvideFiles;
          option_include_paths = List.map (Util.replace_vroot !vroots) !include_paths;
          option_define_macros = !define_macros;
          option_safe_mode = !safe_mode;
          option_header_whitelist = !header_whitelist;
          option_use_java_frontend = !useJavaFrontend;
          option_enforce_annotations = !enforceAnnotations;
          option_allow_undeclared_struct_types = !allowUndeclaredStructTypes;
          option_data_model = !dataModel
        } in
        print_endline filename;
        let emitter_callback (packages : package list) =
          match !outputSExpressions with
          | Some target_file ->
            Printf.printf "Emitting s-expressions to %s\n" target_file;
            SExpressionEmitter.emit target_file packages          
          | None             -> ()
        in
        verify ~emitter_callback:emitter_callback !stats options !prover
          filename !breakpoint_lino !query !context_export_file !export_lino !emitHighlightedSourceFiles;
        allModules := ((Filename.chop_extension filename) ^ ".vfmanifest")::!allModules
      end
    else if Filename.check_suffix filename ".o" then
      allModules := ((Filename.chop_extension filename) ^ ".vfmanifest")::!allModules
    else if List.exists (Filename.check_suffix filename) [ ".so"; ".dll"; ".dll.vfmanifest" ] then
      begin
        let filename =
          if Filename.check_suffix filename ".so" then (Filename.chop_extension filename) ^ ".dll.vfmanifest"
          else if Filename.check_suffix filename ".dll" then (filename ^ ".vfmanifest") 
          else filename
        in
        allModules := filename::!allModules;
      end
    else if Filename.check_suffix filename ".vfmanifest" then
      allModules := filename::!allModules
    else
      begin
        print_endline ("Don't know what to do with file \'" ^ filename ^ "\'."); 
        exit 1
      end
  in
  let usage_string =
    Verifast.banner ()
    ^ "\nUsage: verifast [options] {sourcefile|objectfile}\n"
  in
  if Array.length Sys.argv = 1
  then usage cla usage_string
  else begin
    let process_file filename =
      if !verbose = -1 then Printf.printf "\n%10.6fs: processing file %s\n" (Perf.time()) filename;
      let result = process_file filename in
      if !verbose = -1 then Printf.printf "%10.6fs: done with file %s\n\n" (Perf.time()) filename;
      result
    in
    parse cla process_file usage_string;
    if not !compileOnly then
      begin
        try
          print_endline "Linking...";
          let library_paths = List.map (Util.replace_vroot !vroots) !library_paths in
          let libs = [Filename.concat !Util.bindir "crt.dll.vfmanifest"] in
          let assume_lib = Filename.concat !Util.bindir "assume.dll.vfmanifest" in
          let libs = if !allowAssume then libs @ [assume_lib] else libs in
          let allModules = libs @ List.rev !allModules in
          if !verbose = -1 then Printf.printf "\n%10.6fs: linking files: %s\n\n" (Perf.time()) (String.concat " " allModules);
          let dllManifest =
            if !emitDllManifest then Some (!dllManifestName) else None
          in
          link_program !vroots library_paths (!isLibrary) allModules dllManifest !exports;
          if (!linkShouldFail) then 
            (print_endline "Error: link phase succeeded, while expected to fail (option -link_should_fail)."; exit 1)
          else print_endline "Program linked successfully."
        with
          LinkError msg when (!linkShouldFail) -> print_endline msg; print_endline "Link phase failed as expected (option -link_should_fail)."
        | LinkError msg -> print_endline msg; exit 1
        | CompilationError msg -> print_endline ("error: " ^ msg); exit 1
      end
  end
