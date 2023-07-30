`ifndef RGGEN_BACKDOOR_PKG_SV
`define RGGEN_BACKDOOR_PKG_SV

`ifdef RGGEN_ENABLE_BACKDOOR
package rggen_backdoor_pkg;
  typedef virtual rggen_backdoor_if rggen_backdoor_vif;

  class rggen_backdoor_if_store;
`ifndef XILINX_SIMULATOR
    protected rggen_backdoor_vif  vif[string];

    function void set(string hdl_path, rggen_backdoor_vif vif);
      string  path;
      path            = normalize_hdl_path(hdl_path);
      this.vif[path]  = vif;
    endfunction

    function rggen_backdoor_vif get(string hdl_path);
      return vif[hdl_path];
    endfunction
`else
    class rggen_backdoor_if_wrapper;
      rggen_backdoor_vif  vif;
      function new(rggen_backdoor_vif vif);
        this.vif  = vif;
      endfunction
    endclass

    protected rggen_backdoor_if_wrapper vif_wrapper[string];

    function void set(string hdl_path, rggen_backdoor_vif vif);
      string  path;
      path                    = normalize_hdl_path(hdl_path);
      this.vif_wrapper[path]  = new(vif);
    endfunction

    function rggen_backdoor_vif get(string hdl_path);
      return vif_wrapper[hdl_path].vif;
    endfunction
`endif
    protected function string normalize_hdl_path(string path);
      string  normalized_path;
      for (int i = 0;i < path.len();++i) begin
        if ((path[i] != "\\") && (path[i] != " ")) begin
          normalized_path = {normalized_path, path[i]};
        end
      end
      return normalized_path.tolower();
    endfunction

    static  protected rggen_backdoor_if_store store;

    static function rggen_backdoor_if_store get_store();
      if (store == null) begin
        store = new;
      end
      return store;
    endfunction
  endclass

  function automatic void set_backdoor_vif(
    string              hdl_path,
    rggen_backdoor_vif  vif
  );
    rggen_backdoor_if_store store;
    store = rggen_backdoor_if_store::get_store();
    store.set(hdl_path, vif);
  endfunction

  function automatic rggen_backdoor_vif get_backdoor_vif(string hdl_path);
    rggen_backdoor_if_store store;
    store = rggen_backdoor_if_store::get_store();
    return store.get(hdl_path);
  endfunction
endpackage
`endif

`endif
