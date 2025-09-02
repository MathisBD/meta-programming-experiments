let extract (id : Libnames.qualid) : unit =
  Log.printf "extracting %s" (Pp.string_of_ppcmds @@ Libnames.pr_qualid id);
  let opaque_access = Global.{ access_proof = (fun _ -> None) } in
  Extraction_plugin.Extract_env.full_extraction ~opaque_access (Some "tmp.ml") [ id ];
  Log.printf "done"
