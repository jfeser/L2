module P = Limited_process.Make(Process_info_linux)
include Timeout_cli.Make(P)
