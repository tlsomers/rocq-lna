#!/usr/bin/bash

# Comment out copies of non existing compcert files in installer
sed -i 's/cp source.coq-compcert/# cp source/' '/platform/windows/create_installer_windows.sh'

# Comment out coqide related files
sed -i '/^cp "source\/${ide_name}/ s/^/# /' '/platform/windows/create_installer_windows.sh'
sed -i '/{IDE_NAME}/ s/^/; /' '/platform/windows/Coq.nsi'
sed -i "s/!define MUI_ICON/; !define MUI_ICON/" '/platform/windows/Coq.nsi'

# Install the EnVar plugin downloaded and unpacked in 'Download EnVar Plugin' step
sed -i 's|rm -rf source|rm -rf source\
rsync -a ../windows/envar/ ./nsis-3.06.1|' '/platform/windows/create_installer_windows.sh'

# Use the EnVar plugin to add installation dir to PATH
sed -i 's|SetOutPath "$INSTDIR\\bin\\"|SetOutPath "$INSTDIR\\bin\\"\
  EnVar::AddValue "PATH" "$INSTDIR\\bin"|' '/platform/windows/Coq.nsi'