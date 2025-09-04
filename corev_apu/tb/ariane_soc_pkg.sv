package ariane_soc;
  // M-Mode Hart, S-Mode Hart
  localparam int unsigned NumTargets = 2;
  // Uart, SPI, Ethernet, reserved
  localparam int unsigned NumSources = 30;
  localparam int unsigned MaxPriority = 7;

  localparam NrSlaves = 2; // actually masters, but slaves on the crossbar

  typedef enum int unsigned {
    DRAM     = 0,
    GPIO     = 1,
    Ethernet = 2,
    SPI      = 3,
    Timer    = 4,
    UART     = 5,
    PLIC     = 6,
    CLINT    = 7,
    ROM      = 8,
    Debug    = 9,
    HPS      = 10,
    LSM      = 11
  } axi_slaves_t;

  localparam NB_PERIPHERALS = Debug + 2; //Debug + 1;

  localparam logic[63:0] DebugLength    = 64'h1000;
  localparam logic[63:0] ROMLength      = 64'h3F_FFFF; //64'h10000;
  localparam logic[63:0] CLINTLength    = 64'hC0000;
  localparam logic[63:0] PLICLength     = 64'h3FF_FFFF;
  localparam logic[63:0] UARTLength     = 64'h1000;
  localparam logic[63:0] TimerLength    = 64'h1000;
  localparam logic[63:0] SPILength      = 64'hFF; //64'h800000;
  localparam logic[63:0] EthernetLength = 64'h10000;
  localparam logic[63:0] GPIOLength     = 64'h1000;
  localparam logic[63:0] HPSLength      = 64'h800000;
`ifdef NEXYS_VIDEO
  localparam logic[63:0] DRAMLength     = 64'h20000000; // 512MByte of DDR on Nexys video board
`else
  localparam logic[63:0] DRAMLength     = 64'h01_FFBF_FFFF; //64'h40000000; // 1GByte of DDR (split between two chips on Genesys2) 
`endif
  localparam logic[63:0] SRAMLength     = 64'h1800000;  // 24 MByte of SRAM
  localparam logic[63:0] LSMLength     = 64'h07FF_FFFF;
  // Instantiate AXI protocol checkers
  localparam bit GenProtocolChecker = 1'b0;

  typedef enum logic [63:0] {
    DebugBase    = 64'h0000_0000,
    ROMBase      = 64'h101_0000_0000, //64'h0001_0000,
    CLINTBase    = 64'h0200_0000,
    PLICBase     = 64'h0C00_0000,
    UARTBase     = 64'h1000_0000,
    TimerBase    = 64'h1800_0000,
    SPIBase      = 64'h101_00C0_0000, //64'h2000_0000,
    EthernetBase = 64'h3000_0000,
    GPIOBase     = 64'h4000_0000,
    DRAMBase     = 64'h180_0000_0000, //64'h8000_0000,
    HPSBase      = 64'hFF80_0000,
    LSMBase      = 64'h101_0400_0000
  } soc_bus_start_t;

  localparam NrRegion = 1;
  localparam logic [NrRegion-1:0][NB_PERIPHERALS-1:0] ValidRule = {{NrRegion * NB_PERIPHERALS}{1'b1}};

endpackage