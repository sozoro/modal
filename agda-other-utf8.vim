if exists('g:agda#glyphs')
  call extend(g:agda#glyphs,
    \{ ','      : '⸴'
    \, '\|\|-'  : '⊩'
    \, '\|\|-/' : '⊮'
    \, '/\|\|-' : '⊮'
    \, '\|\|'   : '‖'
    \})
  runtime agda-utf8.vim
endif
