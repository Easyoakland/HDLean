# List of people complaining about new HDL languages and saying that verification is what needs to be easier:

-  Almost every couple of years (and once a decade for something "big") there is a new development in the area mostly driven either by clueless software guys that wandered outisde their turf into hardware territory, or some university chair that sits in the undefined limbo between hardware and software (usually doing something in the realm of CGRAs) that has to justify its existence by offering a PhD to some guy that will create a new RTL IR or another deadborn HLS. Developing hardware is a solved problem. Has been for decades. And no, writing a sentence in your white paper that says something like "existing HDLs operate on gates and cycles and its not an appropriate level of abstraction for us" is not enough of a justification. If you need a fancy pseudo-DSL to hold your hand to be able to describe simple datapaths and FSMs for you then you wouldnt be able to develop anything hardware related that is remotely useful. You cannot abstract away the essence of this engineering task. What we actually need is a tighter verification loops and better (and more accessible) verification methodology so that hardware development is less daunting in the first place, not another DSL-to-RTL translator (even if extensible, like in calyx case) [^1]
-  Almost every couple of years (and once a decade for something "big") there is a new development in the area mostly driven either by clueless software guys that wandered outisde their turf into hardware territory, or some university chair that sits in the undefined limbo between hardware and software (usually doing something in the realm of CGRAs) that has to justify its existence by offering a PhD to some guy that will create a new RTL IR or another deadborn HLS. Developing hardware is a solved problem. Has been for decades. And no, writing a sentence in your white paper that says something like "existing HDLs operate on gates and cycles and its not an appropriate level of abstraction for us" is not enough of a justification. If you need a fancy pseudo-DSL to hold your hand to be able to describe simple datapaths and FSMs for you then you wouldnt be able to develop anything hardware related that is remotely useful. You cannot abstract away the essence of this engineering task. What we actually need is a tighter verification loops and better (and more accessible) verification methodology so that hardware development is less daunting in the first place, not another DSL-to-RTL translator (even if extensible, like in calyx case) [^2]
-
    ```
    The OP makes an interesting point but it doesn't point out the main problem with high level hardware languages: these kind of languages don't allow you to describe the hardware you want exactly, they only allow you to describe their functionality and then they generate a hardware for said functionality. The problem is that you will end up with a hardware that is less optimized than if you were to design it in Verilog.

    I work at a very big semiconductor company and we did some trials with implementing the exact same hardware we had in Verilog but on an high level HDL and while development could be faster, we ended up with worse PPA (Power, Performance and Area). If you try to improve this PPA, you just end up bypassing the advantages of high level HDLs.

    On top of that, it raises a lot of questions on verification: are you going to do verification (testbenches) in the Chisel code or in the generated Verilog code from Chisel? If you do it in Chisel, how do you prove that Chisel didn't introduce bugs in the generated Verilog code (which is what you will end up shipping to the foundry for tape out after synthesis and place & route)? If you do it in the generated Verilog code, how do you trace the bugs back to the Chisel code?

    I do think that we need a new language but not for design. Verilog/System Verilog is fine for hardware design, we don't need to reinvent the wheel here. We will always end up in Verilog in our synthesis and quite frankly, we don't spend that much time writing Verilog for hardware design. Hardware design is 5 lines of code and that's it. The real cost of hardware development is the other side of the coin, which is hardware verification.

    If hardware design is 5 lines of code, hardware verification is 500 lines. Writing testbenches and developing hardware verification environments and flows is essentially normal programming and we are stuck in System Verilog for that, which is a very bad programming language. Using System Verilog as a programming language is so prone to unintended bugs in your testbenches and bad programming constructs.

    This is what we should try to improve, verification not design. We spend far too much time in hardware verification and a lot of that time is spent dealing with pitfalls from System Verilog as a programming language.

    I wish people would be investing more thinking here rather than trying to make hardware design friendlier for programmers.
    ```
    [^3]
-
    ```
    I've said as much before but I find the issue with alternative HDLs Vs SystemVerilog is they concentrate on fixing annoying and frustrating things but don't address the really hard issues in hardware design and can actually make them harder.

    For example SystemVerilog has no real typing which sucks, so a typical thing to do is to build a massively improved type system for a new HDL. However in my experience good use of verilog style guides and decent linting tools solves most of the problem. You do still get bugs caused by missed typing issues but they're usually quickly caught by simple tests. It's certainly annoying to have to deal with all of this but fundamentally if it's all made easier it's not significantly improving your development time or final design quality.

    Another typical improvement you'll find in an alternative HDL is vastly improved parameterization and generics. Again this is great to have but mostly makes tedious and annoying tasks simpler but doesn't produce major impact. The reason for this is writing good HDL that works across a huge parameterisation space is very hard. You have to verify every part of the parameter space you're using and you need to ensure you get good power/performance/area results out of it too. To do this can require very different micro architectural decisions (e.g. single, dual and triple issue CPUs will all need to be built differently improved parameterization doesn't save you from this). Ultimately you often only want to use a small portion of the parameter space anyway so just doing it in system verilog possibly with some auto generated code using python works well enough even if it's tedious.

    So if the practical benefits turn out to be minor why not take all the nice quality of life improvements anyway? There's a large impact on the hard things. From a strictly design perspective these are things like clock domain crossing, power, area and frequency optimization. Here you generally need a good understanding of what the actual circuit is doing and to be able to connect tool output (e.g. the gates your synthesis tool has produced) and your HDL. Here the typical flow of HDL -> SystemVerilog -> tool output can become a big problem. The HDL to SystemVerilog step can produce very hard to read code that's hard to connect to your input HDL. This adds a new and tricky mental step when you're working with the design, first understand the circuit issue then map that to the hard to read SystemVerilog then map that to your HDL and work out what you need to change.

    Outside of design alone a major cost of building silicon is verification. Alternative HDLs generally don't address this at all and again can make it harder. Either you entirely simulate the HDL itself which can be fine but then you're banking on minimal bugs in that simulator and there's no bugs in the HDL -> SystemVerilog step. Alternatively you simulate the SystemVerilog directly with an existing simulator but then you've got the HDL to SystemVerilog mapping problem all over again.

    I think my ideal HDL at this point is a stripped down SystemVerilog with a good type system, better generative capability that crucially produces plain system verilog that's human readable (maintaining comments, signal and module names and module hierarchy as much as possible).
    ```
    [^3]
-
    ```

    IshKebab on Dec 27, 2023 | parent | prev | next [–]

    > However in my experience good use of verilog style guides and decent linting tools solves most of the problem. You do still get bugs caused by missed typing issues but they're usually quickly caught by simple tests.

    Decent linting tools are really expensive. And even it verif does catch all these simple typing mistakes, they still cost a huge amount of time!

    I think the real issue with most of these "compile to Verilog" tools is that all the vendor tools work with SystemVerilog, and now you're debugging autogenerated code, which sucks.

    Another huge issue is formal verification. The tools only understand SVA so you basically have to be using SystemVerilog.

    > I think my ideal HDL at this point is a stripped down SystemVerilog with a good type system, better generative capability that crucially produces plain system verilog that's human readable (maintaining comments, signal and module names and module hierarchy as much as possible).

    I 100% agree here. There's a gazillion things you could fix in SystemVerilog and still have something that compiles to something similar enough that it's easy to debug. Kiiind of like Typescript for SystemVerilog. I wonder if anyone is working on that.
    ```
    [^3]
-
    ```
    If a new HDL language doesn’t have simulation capabilities baked in its next to useless. See: hardcaml and amaranth.

    The hard part has never been writing HDL, it’s verifying HDL and making the verification as organized and as easy as possible. Teams spend something like 20% of time on design and 80%+ on verification allegedly (definitely true at my shop).

    Edit: I see it’s tightly integrated with cocotb which is good. But someone needs to take a verification-first approach to writing a new language for HDL. It shouldn’t be a fun after thought, it’s a bulk of the job.
    ```
    [^4]
- At my shop verification to design time is like 10/1 or more. RTL is generated via Perl scripts. Nobody is coding directly at RTL level here. It's just for debugging. [^4]
- [^5]
    ```
    Our study data continues to underline a consistent truth: 60–70% of engineering effort in chip projects belongs in verification. Traditional chipmakers have internalized this, pouring resources into testbenches, emulation, and coverage analysis.

    By contrast, many system companies underestimate verification at the outset. They view it as overhead rather than the lifeblood of silicon success. The result is predictable: bugs escape pre-silicon, only to surface in the lab. That gap is one of the biggest contributors to today’s lower first-silicon success rates.
    ```

# Talks
- Satnam Singh on functional programming for hardware design with strong emphasis on verification [^6]

[^1]: https://news.ycombinator.com/item?id=39510793
[^2]: https://news.ycombinator.com/item?id=29313350#29315204
[^3]: https://news.ycombinator.com/item?id=38781273
[^4]: https://news.ycombinator.com/item?id=43962138
[^5]: https://blogs.sw.siemens.com/verificationhorizons/2025/09/03/why-first-silicon-success-is-getting-harder-for-system-companies/
[^6]: https://www.youtube.com/live/1oBOu6wX8lc?t=1625s
