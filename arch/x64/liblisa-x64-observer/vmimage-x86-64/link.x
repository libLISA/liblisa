EXTERN(DATA_END);

SECTIONS
{
    . = 0x00001eecb3620000;

    .text : ALIGN(0x1000)
    {
        *(.text .text* .ltext .ltext*)
    }

    .bootloader : ALIGN(0x1000)
    {
        *(.bootloader)
    }

    .data.rel.ro : ALIGN(0x1000)
    {
        *(.data.rel.ro*)
    }

    .got : ALIGN(0x1000) 
    {
        *(.got .got*)
    }

    .data : ALIGN(0x1000)
    {
        *(.data .data.*)
        *(.ldata .ldata.*)
    }

    .rodata : ALIGN(0x1000) 
    {
        *(.rodata .rodata.*)
        *(.lrodata .lrodata.*)
    }

    .bss : ALIGN(0x1000)
    {
        *(COMMON)
        *(.bss .bss*)
        *(.lbss .lbss*)
        *(.gnu.linkonce.b*)
    }

    .bootloader-config : ALIGN(0x1000)
    {
        *(.bootloader-config .bootloader-config*)
    }

    DATA_END = .;

    /DISCARD/ :
    {
        *(.eh_frame .eh_frame_hdr)
    }
}