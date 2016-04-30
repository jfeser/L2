module P = Limited_process.Make(Process_info_osx)
include Timeout_cli.Make(P)
