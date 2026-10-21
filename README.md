# asr64_patcher
Patch ASR image-signature checks on ARM64 and ARMv7k watchOS 1-8 binaries.

## Build
`make`

## Usage

1. Extract binary from the ramdisk using
   [img4](https://github.com/xerub/img4lib) and [hfsplus](https://github.com/justtestingafewthings/libdmg-hfsplus):

   ```sh
   img4 -i ramdisk.img4 -o ramdisk.raw
   hfsplus ramdisk.raw extract usr/sbin/asr asr
   ```

2. Preview the patch, then write the output:

   ```sh
   ./asr64_patcher --dry-run asr
   ./asr64_patcher asr asr_patched
   ```

3. Resign patched ASR binary
    - `ldid -e asr > ents.plist`
    - `ldid -Sents.plist asr_patched`
