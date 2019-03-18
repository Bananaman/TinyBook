--[[

    Project:   "TinyBook: Compact Spellbook"
    Author:    VideoPlayerCode
    URL:       https://github.com/VideoPlayerCode/TinyBook
    License:   Apache License, Version 2.0
    Copyright: Small portions of code (mainly the general XML GUI structure) originates from
               Blizzard's "FrameXML/SpellBookFrame.lua" and "FrameXML/SpellBookFrame.xml",
               extracted from the World of Warcraft 2.4.3 client, for purposes of perfectly
               replicating the visual look and feel of the original spellbook. All other code,
               including all functions, are written by and the copyright of VideoPlayerCode.

]]

------
-- Optimizing Frequently-Used Globals
--
-- Local variables are very fast as they reside in virtual machine registers, and are accessed directly by index.
-- Global variables on the other hand, reside in a lua table (_G / _ENV) and as such are accessed by a hash lookup.
--
-- We will create local variables for all globals that we *VERY FREQUENTLY* access. That means things like being
-- called hundreds of times in a row, or being used inside of tight loops. We don't create locals for "everything",
-- since that would be a massive waste of time (and lines of code) if those globals are barely used anyway.
------

-- WoW APIs

local CooldownFrame_SetTimer = CooldownFrame_SetTimer;
local GetCVar = GetCVar;
local GetSpellAutocast = GetSpellAutocast;
local GetSpellCooldown = GetSpellCooldown;
local GetSpellName = GetSpellName;
local GetSpellTexture = GetSpellTexture;
local HasPetSpells = HasPetSpells;
local IsPassiveSpell = IsPassiveSpell;
local IsSelectedSpell = IsSelectedSpell;
local SetCVar = SetCVar;

-- WoW Constants and Variables

local NORMAL_FONT_COLOR = NORMAL_FONT_COLOR;
local PASSIVE_SPELL_FONT_COLOR = PASSIVE_SPELL_FONT_COLOR;
local _; -- Common "temp" variable, localized to avoid tainting global space.

-- Built-in Lua Functions

local _G = _G; -- Global table: We frequently use it to dynamically lookup global variables.
local assert = assert;
local ceil = ceil;
local debugstack = debugstack;
local error = error;
local format = format;
local ipairs = ipairs;
local pairs = pairs;
local select = select;
local strlen = strlen;
local tconcat = table.concat;
local tostring = tostring;
local type = type;
local unpack = table.unpack or unpack;

-- Turn some of our Globals (other files) into Locals

local TSB_SpellBookFrame; -- Used a LOT by most functions! Defined in XML, so THIS LOCAL VARIABLE is NIL until TSB_SpellBookFrame_OnLoad assigns it.

-- Turn some of our Globals (this file) into Locals
-- NOTE: By pre-declaring these names as local, any "X = 1" assignment or "function X()" will write to the LOCAL variable.

local TSB_CombatLockdown; -- Used by tons of functions to check if we're allowed to modify frames or if we're in lockdown. NOTE: We'll make this a global TOO.
local TSB_EventQueue; -- Can sometimes be called very frequently while we're in combat. NOTE: We'll make this a global TOO.
local TSB_GetSpellID; -- Called by EVERY function that needs to know what spell a button contains! NOTE: We'll make this a global TOO, to allow 3rd party access.
local TSB_SpellBook_GetCurrentPage; -- Used inside of TSB_GetSpellID, which is called a lot.
local TSB_SpellBook_SetCurrentPage; -- Not called frequently, but is here to avoid the "weirdness" of only making the getter local.
local TSB_SpellButton_UpdateButton; -- Called super frequently in response to all kinds of navigation and spell-related events.
local TSB_SpellButton_UpdateSelection; -- Used by TSB_SpellButton_UpdateButton.

------
-- Constants
------

TSB_VERSION = 1000000; -- Version: "1.000.000" (format is MAJOR.MINOR.PATCH).
local BAD_SPELL_ID = -1000; -- Used internally to signal when a requested spell ID slot isn't within our SPELL_ID_LIST range. (Legal spells use 1+).
local SPELL_ID_LIST = {}; -- Our compact spell list for the current "spell school" tab.
local SPELL_ID_LIST_COUNT = 0; -- How many items in SPELL_ID_LIST.
local SPELL_ID_TAB_MAX = 0; -- Highest possible Spell ID in the current "spell school" tab.
TSB_MAX_SPELLS = 1024; -- Same number as Blizzard's book, but replicated here to protect against changes. Is GLOBAL to allow TSB_RankViewer access!
local TSB_MAX_SKILLLINE_TABS = 8; -- Same number as Blizzard's book, but replicated here to protect against changes.
local TSB_SPELLS_PER_PAGE = 12; -- Same number as Blizzard's book, but replicated here to protect against changes.
local BOOKTYPE_PET = BOOKTYPE_PET; -- From Blizzard's UI.
local BOOKTYPE_SPELL = BOOKTYPE_SPELL; -- From Blizzard's UI.
local TSB_SPELLBOOK_PAGENUMBERS = {}; -- Tracks which page we are currently on within each "spell school" tab.
local TSB_FRAME_TAB_LIST = {}; -- Tracks what bottom-tabs our spellbook has and what order they appear in.

------
-- Helper Functions
------

local function print(msg)
    DEFAULT_CHAT_FRAME:AddMessage(msg);
end

-- Safely sets or hooks script handlers on a frame, without tainting Blizzard's scripts or overwriting any existing scripts.
local function hookScript(frame, script, fn)
    -- NOTE: "HookScript" securely adds actions after the existing handler, without overwriting/tainting the original script,
    -- but it cannot execute (does nothing) if no script exists. So we'll dynamically "SetScript" instead in that case.
    if (frame:GetScript(script)) then
        frame:HookScript(script, fn);
    else
        frame:SetScript(script, fn);
    end
end

-- Silences (simply ignores) all PlaySound/PlaySoundFile calls that are executed by your inner "fn" code.
-- NOTE: This does NOT stop/silence any already-playing sound effects, which began playing BEFORE doSilently() was called!
local function doSilently(fn)
    local sfxVal = GetCVar("Sound_EnableSFX");
    SetCVar("Sound_EnableSFX", 0);
    fn();
    SetCVar("Sound_EnableSFX", sfxVal);
end

------
-- Combat Lockdown and Event Queue Handling
-- NOTE: This is necessary because we aren't Blizzard, so we aren't allowed to modify "secure frames" while in combat!
-- See "https://wow.gamepedia.com/API_InCombatLockdown" for a list of FORBIDDEN ACTIONS while in combat, which includes:
-- * Programatic modification of macros or bindings is not allowed while in combat.
-- * Some things can't be done on "Protected"/"Secure Template" frames, their parents, or any frame they are anchored to while in combat. These include:
-- * 1. Hiding the frame using Hide widget method. (Except via "HideUIPanel()", which still works.)
-- * 2. Showing the frame using Show widget method. (Except via "ShowUIPanel()", which still works.)
-- * 3. Changing the frame's attributes (such as the custom attributes which are used by Blizzard secure templates to set up their behavior).
-- * 4. Moving the frame by setting its points or anchors (but movements initiated by user on EnableMouse frames are allowed while in combat).
-- * If you attempt any of those actions while in combat, the calls are simply ignored (no error is thrown, and execution continues).
-- * However, if you log in while in combat, there's a short grace period where addons CAN create/modify secure content. Tested with this addon
--   by running ReloadUI in combat, and then rapidly opening the spellbook and successfully switching to a different tab (attribute changes)
--   before "PLAYER_REGEN_ENABLED" (out of combat) had fired again. This means we DON'T need to worry about login/reloadui; only "real combat" matters.
--   That's further verified by the fact that the "InCombatLockdown()" API is ALWAYS FALSE when logging in/reloading, even if you're actually in combat.
-- * Furthermore, there's a brief grace period AFTER "PLAYER_REGEN_DISABLED" (combat) fires, and the actual lockdown happens. Which means
--   that it's possible to perform some "oh shit"-cleanup immediately when combat begins, such as hiding protected/securetemplate frames, etc.
-- * The safest solution is to hide all secure frames and queue up any events that happen to them in combat, and then simply reopen the frames again
--   and re-play all queued events *after* combat ends, when it's finally safe to react to events and modify the frames again.
------

TSB_CombatLockdown = {};
_G.TSB_CombatLockdown = TSB_CombatLockdown; -- Make a global variable too.
TSB_CombatLockdown.inCombat = false; -- Flag which always reflects the combat state and can be checked manually.
TSB_CombatLockdown.callbacks = {};

TSB_CombatLockdown.frame = CreateFrame("Frame");
TSB_CombatLockdown.frame:SetScript("OnEvent", function(self, event, ...)
    -- The events fire multiple times in a row, so we'll avoid the duplicate multi-firings by only triggering if the state changes.
    -- NOTE: We only listen to two events, so if "PLAYER_REGEN_DISABLED" it means we're in combat, otherwise we've left combat!
    local newInCombatState = (event == "PLAYER_REGEN_DISABLED");
    if (newInCombatState == TSB_CombatLockdown.inCombat) then return; end -- Skip if repeat of the same value.
    TSB_CombatLockdown.inCombat = newInCombatState;
    for _,fn in pairs(TSB_CombatLockdown.callbacks) do
        fn(TSB_CombatLockdown.inCombat);
    end
end);
TSB_CombatLockdown.frame:RegisterEvent("PLAYER_REGEN_DISABLED");
TSB_CombatLockdown.frame:RegisterEvent("PLAYER_REGEN_ENABLED");

function TSB_CombatLockdown:registerCallback(identifier, fn, instantCall)
    self.callbacks[identifier] = fn;
    if (instantCall) then -- Optional: Immediately call the callback with the current state.
        fn(self.inCombat);
    end
end

function TSB_CombatLockdown:unregisterCallback(identifier)
    self.callbacks[identifier] = nil;
end

TSB_EventQueue = {};
_G.TSB_EventQueue = TSB_EventQueue; -- Make a global variable too.
TSB_EventQueue.events = {};

function TSB_EventQueue:addEvent(handler, object, event, ...)
    self.events[#self.events+1] = {
        ["handler"] = handler, -- Event handler function.
        ["object"] = object, -- Which object the event occurred on.
        ["event"] = event, -- The name of the event.
        ["args"] = { ["n"] = select("#", ...), ... }, -- Specially packed varargs to preserve intermixed/trailing nil values.
    };
end

function TSB_EventQueue:runEvents()
    -- Do nothing if there are no events waiting in the queue.
    if (#self.events == 0) then return 0, 0; end

    -- Copy table reference and RESET internal event table, to ensure NO NEW EVENTS can be added to the queue while we iterate.
    -- NOTE: And since Lua is single-threaded, there is ALSO zero risk that the GUI will go into "combat lockdown" again WHILE we process the queue!
    local events = self.events;
    self.events = {};

    -- Keeps track of how many events we've actually executed in this passthrough.
    local runCount = 0;
    local eventCount = #events;

    -- There are certain "extremely spammy" events (such as "spell cooldown started/ended") which can queue up HUNDREDS OF THOUSANDS of instances
    -- per combat session, and we ONLY want to fire those ONCE per unique handler+object combination to AVOID SLOWDOWNS when running the queue!
    -- NOTE: We'll use TABLES AND FUNCTIONS AS KEYS in this table. That's a legal Lua feature (http://www.lua.org/manual/5.1/manual.html#2.2);
    --   "tables implement associative arrays; that is, arrays that can be indexed not only with numbers, but with any value (except nil)".
    --   And lookups will be even faster than string keys, since Lua just has to check if a specific table/function's memory address exists
    --   as a table key! This does however have the side-effect that it tracks EXACT instances, based on their memory address, so remember that!
    -- NOTE: The de-duplication table structure is "uniqueEvents[eventName string][eventObject table][eventHandler function]".
    -- NOTE: None of the events below have any interesting arguments, so we'll de-duplicate them on an "object+handler" combination basis
    --   without any regard for their arguments! In other words, even if the same events have diff args, we ignore that and de-dupe anyway!
    -- NOTE: This de-duplication code **ONLY MATTERS** if our spellbook frame is allowed to REMAIN VISIBLE while in-combat. If we've instead
    --   hidden the frame, the OnHide handlers actually unregister ALL addon events EXCEPT "SPELLS_CHANGED" and "LEARNED_SPELL_IN_TAB", which
    --   means that NOTHING "spammy" will get added to the event queue while combat is ongoing! However, this code is still a great safety net
    --   just in case combat-spam events SOMEHOW sneak their way into the queue, OR in case we decide to allow the addon to stay open in combat.
    --   However, the latter is extremly unlikely, since 3rd party addons are in "lockdown" while in combat, so the frame wouldn't allow navigation,
    --   and we'd just pointlessly accumulate a ton of duplicate, spammy "in-combat events" while obscuring the player's screen with a "locked" window.
    --   Furthermore, if we ACTUALLY queue all events while in combat, we can easily accumulate 20 thousand events per minute, which may impact memory!
    --   And all of that work for WHAT? A useless spell-frame that can't switch pages/tabs in combat due to Blizzard's lockdown? Pointless!
    local uniqueEvents = {
        -- * SPELL_UPDATE_COOLDOWN (SpellButton + SpellRankButton): This event is an absolute spam-freak. It's triggered twice when you
        --   cast a spell, and every second while you channel a spell, and every time a hunter shoots (since "Auto Shot" is actually
        --   a self-casting spell with an internal cooldown). Multiplied by the 12 spell buttons, this can easily accumulate mountains
        --   of queued events during an intense fight... yet we only actually need to trigger this ONCE per recipient object after combat!
        ["SPELL_UPDATE_COOLDOWN"] = {},
        -- * CURRENT_SPELL_CAST_CHANGED (SpellButton): Instanely spammy event which fires around 3-10 (usually 5) times in a row whenever
        --   you cast ANY spell. Multiply that by the fact that there are 12 buttons listening to this event, and you've got a hell of a lot
        --   of duplicates of this event being queued up after a long fight!
        ["CURRENT_SPELL_CAST_CHANGED"] = {},
        -- * SPELLS_CHANGED (SpellBookFrame): Fires whenever the player's spells change in any way (including trivial changes such as icon,
        --   or larger changes such as gaining/losing a spell (or gaining/losing a pet and therefore its spells)). Doesn't actually trigger
        --   automatically for any gameplay reasons in-combat, but will trigger if the player is navigating the Blizzard spellbook, since
        --   their (poorly coded) spellbook calls "UpdateSpells()" constantly during almost every action, such as pagination and "skill line
        --   tabs" (and bottom-"Spells/Pet" tab) switching, all of which call APIs. If the player views the Blizzard spellbook and navigates
        --   a lot during combat, that can lead to tons of "queued up" duplicates of this event! Either way, this is a very important event
        --   which is USUALLY pointless (whenever it's merely triggered via navigation) but sometimes relates to HUGE changes to the spells
        --   (meaning that we MUST re-build the compact spell list and update our GUI). That's why this event is critically important.
        ["SPELLS_CHANGED"] = {},
        -- * PET_BAR_UPDATE (SpellButton): This triggers whenever the pet bar needs to be re-rendered, such as after summoning/dismissing
        --   a pet, or toggling an autocast skill, or moving a skill on the pet bar, or changing the aggressiveness or follow states. For
        --   pet classes that use a lot of macros to control their pet in combat, this can cause quite a substantial buildup of redundant
        --   events that tell us to update the pet spell buttons, so it's worth de-duplicating these.
        ["PET_BAR_UPDATE"] = {},
        -- Other events used by our addon aren't worth throttling, since they don't happen frequently in combat:
        -- * CRAFT_SHOW/CRAFT_CLOSE (SpellButton): Legacy event which isn't used by the client anymore, but still lingers in Blizzard's spellbook code.
        -- * TRADE_SKILL_SHOW/TRADE_SKILL_CLOSE (SpellButton): "Show" fires once when opening a tradeskill window, and "Close" fires once or twice
        --   when closing a tradeskill window (twice if closed via triggering the skill again; once if closed via the window's X).
        --
        -- There are also very important events where the arguments DO matter, and which we DON'T want to de-duplicate via "uniqueEvents":
        -- * LEARNED_SPELL_IN_TAB (SpellBookFrame): Triggers 1-2 times whenever the player learns a new spell/spellrank/profession. First of all,
        --   this event should never be happening in combat. Secondly, it's very rare and very important (we must always react to it and flash/queue
        --   the appropriate "school tab" EVERY time it fires). And lastly, we need to preserve its args since the argument decides which spell tab
        --   we should "highlight" to show that a new spell has been learned.
        --   ...Actually, "TSB_SpellBookFrame_OnEvent" will IMMEDIATELY process "LEARNED_SPELL_IN_TAB" in combat. It will NEVER be in the queue!
    };

    -- "Re-play" the events as if they just fired now, with the exact same handler, object (target), event name and arguments.
    local skip, prevData, seen;
    for i,data in ipairs(events) do
        -- Compare this event to the PREVIOUS event, and skip if everything (even the arguments) are identical.
        -- NOTE: The intent is to "cull" REPEATED EVENTS ("A, A, A, A"), to lessen the workload after coming back from combat. However,
        -- it doesn't handle INTERLEAVED events ("A, B, A, B"), since that would be way too complex to deal with SAFELY and QUICKLY.
        skip = false;
        if (i >= 2) then -- Start comparing from event 2 and onwards.
            prevData = events[i-1]; -- Look at previous event.
            if (data.handler == prevData.handler and
                data.object == prevData.object and
                data.event == prevData.event and
                data.args.n == prevData.args.n) then
                -- Same handler function, target object, event name and argument count. Now check if all arguments are identical.
                -- NOTE: This WON'T recursively check tables (that'd be slow!). But we know for a fact that none of our events use table arguments!
                skip = true; -- Assume they're identical (skip!); then check for differences.
                if (data.args.n >= 1) then
                    for j=1, data.args.n do -- NOTE: Uses "data.args.n" to successfully loop through "nil" holes in arguments.
                        if (type(data.args[j]) ~= type(prevData.args[j]) or -- Different types.
                            data.args[j] ~= prevData.args[j]) then -- Or same types, but different values. (In case of tables: "NOT exact same object"!)
                            skip = false;
                            break; -- An argument differed. No need to check any more of them.
                        end
                    end
                end
            end
        end

        -- If this event ISN'T being skipped by the regular de-duplicator above, then check the harsher "unique events" de-duplicator instead.
        -- NOTE: The "and data.X" ensures that we don't proceed with empty values, since those would be invalid as table keys further down.
        if ((not skip) and data.event and uniqueEvents[data.event] and data.handler and data.object) then
            seen = uniqueEvents[data.event]; -- Table of all previously seen objects + handlers for the given eventname.
            if (seen[data.object]) then
                if (seen[data.object][data.handler]) then
                    skip = true; -- SKIP: We've already seen this exact object + handler function before.
                else
                    seen[data.object][data.handler] = true; -- RUN: We've now seen this handler function.
                end
            else
                seen[data.object] = { [data.handler] = true }; -- RUN: We've now seen this object + handler function combination.
            end
        end

        -- If we should run this event, we'll do so using a special unpack technique which preserves the exact argument list (including "nil" holes).
        -- NOTE: Unpacking uses the "n" count to ensure that we always unpack EXACTLY as many arguments as the original input, including every "nil".
        -- NOTE: We don't catch external errors that may be thrown by the handler function. We could use pcall() for that, but it's not worth it.
        if (not skip) then
            data.handler(data.object, data.event, unpack(data.args, 1, data.args.n));
            runCount = runCount + 1;
        end
    end

    -- Return how many events we ran, and how many were in the queue.
    return runCount, eventCount;
end

------
-- SpellBook Frame
------

-- List of all SpellButtons, for quick iteration whenever the buttons need to be updated.
-- NOTE: We use this instead of the stupid "SPELLS_CHANGED" event system that Blizzard's own spellbook uses. Theirs runs some functions
-- which then fire that event which then triggers the SAME functions again, which constantly leads to ~6-7 useless repeats in their code. ;-)
-- Our system will instead simply keep track of which GUI buttons exist, and will update them manually without faking "SPELLS_CHANGED".
-- And as a huge upside, this improvement also means that our code is therefore able to distinguish REAL "SPELLS_CHANGED" events properly,
-- allowing us to take those events much more seriously (since they mean we've gained/lost a spell, spell rank, or gained/lost a pet).
TSB_AllSpellButtons = {};

-- Mechanism for signaling to our "ToggleSpellBook" hook that it should "allow" the NEXT call to run Blizzard's code normally.
-- NOTE: This allows us to at-will bypass our "redirect everything to TinyBook" code, and instead use Blizzard's frame.
local allowNextBlizzardSpellBook = false; -- Default to using TinyBook mode.
function TSB_AllowNextBlizzardSpellBook()
    allowNextBlizzardSpellBook = true;
end

-- Opens the TinyBook GUI or changes the active book type (such as spells or pet abilities).
-- NOTE: This isn't meant to be called directly. It's used by our "ToggleSpellBook" API hook (set up during "TSB_SpellBookFrame_OnLoad").
-- NOTE: The "HideUIPanel/ShowUIPanel" calls below are basically like "Hide" and "Show", except that they also
-- tell WoW to treat the frame as a "UI Panel" which stacks on-screen and is closable with Escape, etc.
-- NOTE: The second parameter is OPTIONAL, and lets you force the "IsShown" check to believe that the frame is visible. That's useful
-- if you have a cached visibility state which should be applied to this function rather than the latest frame-visibility. IF specified, the
-- value must be a "truthy" value (such as true, or any other non-nil, non-false value); otherwise the regular "IsShown" check runs instead.
function TSB_ToggleSpellBook(bookType, treatAsShown)
    -- Ensure that we will never receive an empty or invalid bookType value.
    -- NOTE: Blizzard's own spellbook doesn't do this validation and therefore breaks via "/run ToggleSpellBook()" with no/bad args. ;-)
    if (bookType ~= BOOKTYPE_SPELL and bookType ~= BOOKTYPE_PET) then
        bookType = BOOKTYPE_SPELL;
    end

    -- Ignore requests to open/swap to "PET" spells when the player doesn't have a pet.
    local hasPet = HasPetSpells();
    if ((not hasPet) and bookType == BOOKTYPE_PET) then
        return;
    end

    -- Check the active frame state (or use cached "treatAsShown" if provided).
    -- NOTE: We ALWAYS look at the true "IsShown" state if "treatAsShown" is false.
    local isShown = treatAsShown or TSB_SpellBookFrame:IsShown();

    -- Determine whether the request would change to a different book type.
    local isChanged = (TSB_SpellBookFrame.bookType ~= bookType);

    -- Close the spellbook (ensuring that we perform a full refresh if we switch book types).
    HideUIPanel(TSB_SpellBookFrame);

    -- Open the spellbook if it wasn't already open or if we're swapping to a different type.
    if ((not isShown) or isChanged) then
        TSB_SpellBookFrame.bookType = bookType;
        ShowUIPanel(TSB_SpellBookFrame);
    end
end

-- Switches from the Blizzard GUI to the TinyBook GUI, and views the same spellbook type ("Spellbook" or "Pet") and spell-school.
function TSB_BlizzardToTinyBook()
    -- Get the currently active book type (and "spell school" selection) from Blizzard's frame.
    -- NOTE: The fact that we jump to viewing the exact same "spell school" is a very nice advertisement for TinyBook mode, since
    -- it becomes extremely apparent how nice it is to just see 1-2 pages (instead of 5-10 annoying pages of repeated junk ranks).
    local bookType = SpellBookFrame.bookType;
    local changeSkillLine;
    if (bookType == BOOKTYPE_SPELL) then
        changeSkillLine = SpellBookFrame.selectedSkillLine; -- Copy selected "spell school" choice.
    elseif (bookType == BOOKTYPE_PET and (not HasPetSpells())) then
        bookType = BOOKTYPE_SPELL; -- Force "Spellbook" tab since we no longer have a pet; but we won't "changeSkillLine".
    end

    -- Close Blizzard's frame and open the TinyBook frame instead.
    HideUIPanel(SpellBookFrame); -- We allow this to play its close-sound if Blizzard's frame was open.
    doSilently(function()
        HideUIPanel(TSB_SpellBookFrame); -- Silently closes our frame if it was open (we close to ensure next "toggle" will OPEN).
    end);
    TSB_ToggleSpellBook(bookType); -- Open our TinyBook frame at the desired book type (but not yet at the correct "spell school").

    -- Apply the desired "spell school" selection, EVEN IF we are already viewing that exact "spell school" tab.
    -- NOTE: We click the tab even if the spellbook was already set to that tab. That way we guarantee that we'll stop its "new spell" flashing.
    if (changeSkillLine and TSB_SpellBookFrame:IsShown() and TSB_SpellBookFrame.bookType == BOOKTYPE_SPELL) then
        --NOTE: We COULD technically JUST edit the "TSB_SpellBookFrame.selectedSkillLine" property (BEFORE we run "TSB_ToggleSpellBook"),
        --because the most important things such as rebuilding the spell list and marking the active "spell school" tab will be taken
        --care of during "TSB_ToggleSpellBook" and the "OnShow" handler. However, the actual "spell school" tab's on-click handler has
        --a few ADDITIONAL handlers that we really want to run. Mainly to ensure that we run its "stop flashing" handler, to guarantee
        --that flashing "spell school" tabs don't CONTINUE flashing AFTER switching to that exact tab in our TinyBook spellbook.
        --NOTE: Actually, in the case of "Blizzard to TinyBook", there's no big reason to fake a click here (since WE are able to view the
        --desired tab by simply editing the variables). Because the important "stop TinyBook flashing" code is ALREADY taken care of by our
        --reverse hook during the exact moment that the user clicked on any Blizzard tab (see "TSB_EnhanceBlizzardSpellbook" for details).
        --But meh... we'll still keep this click-step here too, just for perfect symmetry between the "To/From Blizzard" code algorithms.
        doSilently(function()
            TSB_SpellBookSkillLineTab_OnClick(_G["TSB_SpellBookSkillLineTab"..changeSkillLine]); -- Silenced to avoid its "school click" sound.
        end);
    end
end

-- Switches from the TinyBook GUI to the Blizzard GUI, and views the same spellbook type ("Spellbook" or "Pet") and spell-school.
-- NOTE: This is part of the "PreClick" handler for "TSB_SpellBookFrameTabButton4" in TinyBook.xml, which uses a special "secure
-- template" trick to open the Blizzard book! However, addons AREN'T ALLOWED to modify the Blizzard spellbook's "current view"
-- variables without causing taint and BREAKING the Blizzard code completely, so the way we "apply the same view settings" is
-- to dynamically (PreClick) rewrite the button's OnClick "open Blizzard spellbook" macro to ALSO send secure clicks to the
-- desired pet/spell school tabs. The final result is that we're able to open Blizzard's spellbook to ANY tab we want!
function TSB_TinyBookToBlizzard()
    -- If the GUI is in combat lockdown, we aren't able to edit attributes on the SecureTemplate frame, so just ignore the call.
    -- NOTE: It should be impossible to ever be in combat here, since our TinyBook frame (with this button) hides itself in combat.
    if (TSB_CombatLockdown.inCombat) then
        return;
    end

    -- Dynamically build a macro which opens the Blizzard spellbook on the same bottom-tab and "spell school" as the TinyBook spellbook.
    local macro = {};
    local sfxVal = GetCVar("Sound_EnableSFX") or "0"; -- Get current SFX-setting (should be a string "1" or "0"; fallback to "0" (off)).

    -- Hide our frame to ensure there aren't any excess frames if "ShowUIPanel" (via "ToggleSpellBook") decides to close panels to make room.
    -- NOTE: This actually isn't necessary thanks to our "HideUIPanel" hook which auto-hides ourselves before Blizzard's spellbook opens,
    -- but it's still a good idea to do it here too, since this macro code becomes much clearer about what it's actually doing.
    macro[#macro+1] = "/run HideUIPanel(TSB_SpellBookFrame)"; -- We allow this to play its close-sound if our frame was open.

    -- Ensure that the Blizzard spellbook is closed, so that the upcoming call to "toggle" will definitely OPEN it.
    macro[#macro+1] = "/console Sound_EnableSFX 0"; -- Silence so that we don't hear their "closing spellbook" sound.
    macro[#macro+1] = "/run HideUIPanel(SpellBookFrame)";
    macro[#macro+1] = "/console Sound_EnableSFX "..sfxVal; -- Restore sound setting.

    -- Open the Blizzard spellbook via the ONLY legal technique (see "TSB_SpellBookFrameTabButton4" in TinyBook.xml for details).
    -- NOTE: Technically, the internal "PlaySound" call will always be the "opening spellbook" rather than the "opening pet" sound, since
    -- the API is being called with "BOOKTYPE_SPELL" here. Also remember that our "ToggleSpellBook/HideUIPanel" hooks mute the original opening
    -- sound and then play the "correct" one based on which spellbook the player actually opened. But since this API call opens the "BOOKTYPE_SPELL"
    -- mode, it'll ALWAYS play the "spellbook" sound. However, this isn't noticeable, since the "opening pet" sound is identical audio-wise. ;-)
    macro[#macro+1] = "/run TSB_AllowNextBlizzardSpellBook()"; -- Allow next "ToggleSpellBook" API to be handled by Blizzard's GUI instead.
    macro[#macro+1] = "/click SpellbookMicroButton"; -- Triggers "ToggleSpellBook(BOOKTYPE_SPELL)". Plays standard non-pet "opening" sound!

    -- Now click on the appropriate "spell school" tab or the "pet bottom-tab", depending on what we want to view.
    macro[#macro+1] = "/console Sound_EnableSFX 0"; -- Silence to avoid the "closing Spellbook, opening Pet book" or "school click" sounds.
    if (TSB_SpellBookFrame.bookType == BOOKTYPE_SPELL) then
        -- NOTE: We click the tab even if the spellbook was already set to that tab. That way we guarantee that we'll stop its "new spell"
        -- flashing. That's important, since "tab1" may flash on TinyBook, user goes to Blizzard, views "tab1" (so we don't want it to flash
        -- anymore), then switches back to TinyBook mode. In that case, it's correct to no longer be flashing the tab in TinyBook mode either.
        macro[#macro+1] = "/click SpellBookSkillLineTab"..TSB_SpellBookFrame.selectedSkillLine; -- Click "spell school" tab.
    elseif (TSB_SpellBookFrame.bookType == BOOKTYPE_PET) then
        macro[#macro+1] = "/click SpellBookFrameTabButton2"; -- Click pet tab; triggers "ToggleSpellBook(BOOKTYPE_PET)".
    end
    macro[#macro+1] = "/console Sound_EnableSFX "..sfxVal; -- Restore sound setting.

    -- Write the new macro text to the Secure Action Button's "macrotext" attribute (which can hold up to 1024 characters).
    -- NOTE: The final macros above are 273 (spell) and 275 (pet) characters long, respectively.
    TSB_SpellBookFrameTabButton4:SetAttribute("macrotext", tconcat(macro, "\n"));
end

function TSB_HandleCombatLockdown(inCombat)
    --[[
    When the player enters combat, we'll hide the TinyBook frame, since Blizzard DOESN'T ALLOW OUR CODE TO RUN PROPERLY
    while the player is in combat. It's the best solution to an unfortunate problem.

    In combat, Blizzard prevents Hiding, Showing, Positioning and Attribute modification on Protected/SecureTemplate frames,
    UNLESS the addon code is written by Blizzard themselves. We aren't Blizzard. Which means that while the player
    is in combat, we're COMPLETELY UNABLE to handle pagination (switching pages/tabs), showing/hiding "spell rank"
    popups, or doing any other kinds of super important updates to the spell list (the spell buttons, to be precise).

    Attempts WERE made to merely "disable" elements, such as the next/prev buttons and the tabs, and to disable all updates
    of the "spell buttons" in the spellbook frame. But it just looked weird and super confusing. Why keep a "dead, disabled"
    spellbook covering up the screen while the player fights? It would just confuse players and make them wonder why
    everything "stops working in combat". Well, that's Blizzard's fault and there is absolutely NOTHING we can do
    about it... There is NO way for us to have a functional spellbook in combat without "US" being BLIZZARD!

    Furthermore, the frame, while visible, listens to TONS of "spell info/casting" game events, to update all buttons.
    But whenever you're IN COMBAT, those events go from firing "perhaps once per minute", to firing HUNDREDS of events
    PER SECOND while in combat (all of the spell-casts, GCD/cooldowns triggering, etc, all cause events to fire). That
    is a MASSIVE workload frenzy. In fact, even the Blizzard spellbook suffers from this problem, since IT *CAN* stay open
    in combat, and listens to those events while you fight, which means HUNDREDS of API calls and GUI updates per second.

    But that brings us to the final solution: Admit that *WE* CAN'T have a functional custom spellbook while in combat,
    and TEACH the user this fact in a very intuitive way which even "feels like a great FEATURE": We AUTOMATICALLY HIDE
    the TinyBook window as soon as the player enters combat, and we REFUSE TO RE-OPEN IT while in combat. This now means
    that the player's screen instantly "cleans itself up" and lets them focus on the combat. But of course, being
    completely unable to open *any* spellbook would be a downgrade. So to solve that, we temporarily route all "open
    spellbook" requests to BLIZZARD'S SPELLBOOK instead, so that WHILE the user is actively in combat, ANY attempts
    to view the spellbook will cause the Blizzard version to appear instead. Furthermore, AFTER combat ends, we'll
    automatically re-open our TinyBook GUI at the exact location the user was viewing before combat began.

    So that's it... we hide the window in combat. It becomes completely obvious to the user that it's related to combat,
    and it avoids all confusion... and best of all -- it frees up the screen for FIGHTING! ;-)
    ]]

    if (inCombat) then
        -- Combat has begun, which means that the WoW GUI enters lockdown soon. Force our spellbook to close if it's visible on-screen!
        -- NOTE: The "HideUIPanel" call is the correct way to hide; exact same method as "TSB_ToggleSpellBook".
        -- NOTE: If the spellbook was visible here, we'll re-open it again after combat (except if player manually opens Blizzard spellbook in combat).
        if (TSB_SpellBookFrame:IsShown()) then
            HideUIPanel(TSB_SpellBookFrame);
            TSB_SpellBookFrame.reopenAfterCombat = true;
        end

        -- Hide the "Switch between Blizzard/TinyBook spellbook" tabs, since we DON'T want the user to try to open the TinyBook spellbook
        -- in combat. *And* the tabs would have position-problems if left visible since we're not allowed to SetPoint their positions in combat.
        -- NOTE: In fact, we're not even allowed to Hide them either, but there's a slight grace period HERE when combat has just begun!
        if (SpellBookFrameTabButton4) then SpellBookFrameTabButton4:Hide(); end
        if (TSB_SpellBookFrameTabButton4) then TSB_SpellBookFrameTabButton4:Hide(); end
    else
        -- First, trigger all events (if any) that were queued while the player was in combat.
        TSB_EventQueue:runEvents();

        -- Ensure that the "Switch between Blizzard/TinyBook spellbook" tabs are in the correct location, and make them visible again.
        TSB_RePosition_FrameTab4();
        if (SpellBookFrameTabButton4) then SpellBookFrameTabButton4:Show(); end
        if (TSB_SpellBookFrameTabButton4) then TSB_SpellBookFrameTabButton4:Show(); end

        -- Automatically open our spellbook again if it was auto-closed due to combat lockdown.
        -- NOTE: The player will see the LATEST TAB/PAGE they were viewing before the frame was closed, which is a super nice feature!
        if (TSB_SpellBookFrame.reopenAfterCombat) then
            TSB_SpellBookFrame.reopenAfterCombat = false;
            if (not TSB_SpellBookFrame:IsShown()) then
                -- Ensure that we open the REGULAR spellbook if the player had a pet before combat but NO LONGER has a pet.
                -- NOTE: This is necessary to ensure a window, since "TSB_ToggleSpellBook" IGNORES calls to open pet book when no pet exists.
                local bookType = TSB_SpellBookFrame.bookType;
                if (bookType == BOOKTYPE_PET and (not HasPetSpells())) then
                    bookType = BOOKTYPE_SPELL;
                end
                TSB_ToggleSpellBook(bookType);
            end
        end
    end
end

local function TSB_EnhanceBlizzardSpellbook()
    -- Ensure that Blizzard's spellbook stacks predictably (the same way as our frame), and that it doesn't easily auto-close itself anymore.
    -- NOTE: See the "UIPanelLayout" section of TinyBook.xml for more information about exactly what this does.
    if (UIPanelWindows["SpellBookFrame"]) then
        -- NOTE: Thankfully, this minor taint of a Blizzard variable doesn't cause any problems for secure code. The "pushable" variable
        -- is only used for some math in "FramePositionDelegate:ShowUIPanel" (FrameXML/UIParent.lua), and isn't sent as argument to any
        -- functions that require secure arguments. So nothing "explodes" due to us overwriting this value. Phew!
        --UIPanelWindows["SpellBookFrame"].pushable = 1;
        -- UPDATE: Actually, this was a PERFECT example of how "devious" hidden taint can be! Writing to the variable above taints the "pushable"
        -- property, which DIDN'T SEEM to cause ANY issues AT ALL. EXCEPT... if you log into the game, then ENTER COMBAT, and THEN press "P" to open
        -- your Blizzard spellbook. The first attempt to open it will FAIL and DO "NOTHING": The "ToggleSpellBook" API will run but then ITS internal
        -- call to "ShowUIPanel" will EXPLODE due to seeing the tainted variable WHILE IN COMBAT (it had ZERO ISSUES at all with that tainted "pushable"
        -- variable if you do your FIRST spellbook opening OUTSIDE combat). Anyway, that "crash" causes their "first ShowUIPanel" call to error/abort
        -- during its important "it's the first time we see that panel this session, let's register it" routines... which means that Blizzard's
        -- SpellBookFrame DOESN'T get FULLY registered as a UI panel, and can NEVER be closed via "escape" from then on. Ugh! So obviously we CANNOT
        -- rely on the method which taints the "pushable" variable above, since that method would break whenever your 1st opening of the spellbook
        -- for the current game session happens to be in combat!

        -- Luckily, there's a way to solve the problem... The first "ShowUIPanel" call to any panel does some work which looks at "UIPanelWindows",
        -- as well as the frame's existing attributes (irrelevant in this case), and then WRITES those settings to the frame's attributes. After
        -- that, ALL future "UI Panel" related functions ONLY read from the FRAME ATTRIBUTES instead of the "UIPanelWindows" table entry.
        --
        -- First, we must somehow coerce Blizzard into PREMATURELY writing all UI panel settings to the SpellBookFrame's attributes. We aren't
        -- allowed to run Blizzard's "ToggleSpellBook" since that would cause it to run with tainted scope and would cause its "write variables
        -- to SpellBookFrame table" to write TAINTED variables to itself and break the spellbook. But luckily, their "ToggleSpellBook" API DOESN'T
        -- REALLY DO ANYTHING except set the "SpellBookFrame.bookType" property and THEN call "ShowUIPanel(SpellBookFrame)", followed by a final call
        -- to "SpellBookFrame_UpdatePages". Well, let's break down how important that stuff really is: Setting bookType is totally unimportant
        -- since they already initialize its value to BOOKTYPE_SPELL in their OnLoad handler. Showing the panel, is obviously extremely important.
        -- As for the final "update the pages" call, it's actually TOTALLY POINTLESS due to one of many bugs in Blizzard's spellbook code; the
        -- fact that their "OnShow" handler ALWAYS calls "SpellBookFrame_Update" which in turn always calls "SpellBookFrame_UpdatePages"! Bingo!
        --
        -- So, that reduces our needs down to a single function: "ShowUIPanel(SpellBookFrame)". Everything then hinges on whether calling that
        -- function from unsafe (non-Blizzard) code would taint anything. Thankfully, the answer is: NO! That function is allowed to open ANY
        -- secure frame and run ANY secure code and will NEVER inherit the tainted scope from its caller! BINGO! (This fact can be verified by
        -- making a small addon which runs "ShowUIPanel(SpellBookFrame)"; you'll be able to cast spells from the opened secure window!)
        --
        -- Therefore we first run "ShowUIPanel" to make the UI Panel system register all SECURE spellbook panel settings as frame attributes!
        -- NOTE: The fact that "ShowUIPanel" runs to completion and successfully registers the panel further proves that the call is somehow
        -- running in secure (non-tainted) mode despite being called from unsafe code. It SEEMS like Blizzard has done something to mark that
        -- function as "run as secure regardless of who called it"... although I don't have any definitive answer.
        -- NOTE: Another relieving fact is that even IF something were to become tainted by us calling "ShowUIPanel" here (which it doesn't
        -- seem to be), ALL future "ShowUIPanel" will be triggered by the user via things like "P" (keyboard) or secure button clicks, which
        -- means the secure code will be running and re-writing those variables for us when the user ACTUALLY opens the spellbook for real.
        -- However, there really doesn't seem to be any taint propagation here, since even "/run ShowUIPanel(SpellBookFrame)" and non-secure
        -- buttons with OnClick handlers are able to run this and open a fully functioning spellbook with zero visible taint problems.
        doSilently(function()
            HideUIPanel(SpellBookFrame); -- Ensure frame is hidden so that ShowUIPanel will actually do something... (Probably not necessary.)
            ShowUIPanel(SpellBookFrame); -- Show it... to force Blizzard to write all "UIPanelWindows" properties to its frame attributes.
            HideUIPanel(SpellBookFrame); -- ... and then hide it immediatley.
        end);

        -- Now the final step hinges on whether we are allowed to taint the ATTRIBUTE or not. And the answer is: We ARE allowed! Nothing breaks,
        -- even in combat! The UI panel system will read THIS attribute on every "ShowUIPanel(SpellBookFrame)" action from now on, and will use
        -- its value to determine how "pushable" the Blizzard spellbook is. The fact that it works can be verified by opening "O" (friends list)
        -- at the same time as viewing the Blizzard spellbook. If the pushable state had still been 0, the spellbook would have closed! :-)
        if (SpellBookFrame:GetAttribute("UIPanelLayout-pushable")) then -- NOTE: Is only "non-nil" if the attribute exists. Which it should.
            -- NOTE: We aren't allowed to write this attribute (or any other) in combat, but we apply this OnLoad which is NEVER in combat.
            SpellBookFrame:SetAttribute("UIPanelLayout-pushable", 1);
        else
            print("Error while loading TinyBook: Unable to set pushability state of Blizzard's frame."); -- Should never happen. Non-fatal error.
        end
    end

    -- Enhance Blizzard's "spell school" tabs by giving them the same, nice, "soft click" that OUR tabs use (in "TSB_SpellBookSkillLineTab_OnClick").
    for tabNum=1, MAX_SKILLLINE_TABS do -- Loop over all of Blizzard's tabs (note no "TSB_" prefix; we use Blizzard's variable this time).
        hookScript(_G["SpellBookSkillLineTab"..tabNum], "PostClick", function(self)
            -- NOTE: We DON'T proceed with handling this click if the Blizzard frame is HIDDEN and yet somehow got clicked (ie. via "/click" macros).
            -- NOTE: "GetChecked()" ensures that Blizzard's OnClick handler has accepted the click and made the tab "checked" (active).
            if (self:GetChecked() and SpellBookFrame:IsShown()) then
                PlaySound("igMainMenuOptionCheckBoxOn");
            end
        end);
    end

    -- Blizzard's original spellbook "frame flashing" code is extremely buggy. We'll fix it by instead syncing the state directly from our
    -- own, much more advanced TinyBook tab flashing system. That fixes ALL of the following stress-inducing bugs/annoyances:
    --
    -- * Blizzard's spellbook ALWAYS CLEARS ALL FLASHING whenever the frame is closed (via either closing the spellbook OR by switching the active
    --   bottom-tab; which causes a close-and-reopen action). This means that you're CONSTANTLY LOSING the "flash" showing WHICH tabs contain new spells!
    -- * Blizzard's spellbook doesn't always start flashing "spell school" tabs if the book is CURRENTLY open WHILE you learn the new spell/ability;
    --   to be specific, it ONLY starts properly if you have PREVIOUSLY HAD a flashing tab during THAT game session (so their flash-code is still running).
    -- * Blizzard's spellbook handles LEARNED_SPELL_IN_TAB in a VERY stupid way. It ONLY starts flashing IF you're viewing "Spellbook" (not the "Pet"
    --   tab). That's a HUGE problem whenever you're viewing the "Pet" tab, learn a normal spell, and then switch to the "Spellbook" tab: NOTHING FLASHES!
    -- * Blizzard's spellbook uses "SpellBookFrame.flashTabs" to keep track of whether anything needs to be flashing, but they've FORGOTTEN to ever set
    --   it back to "false" when they're done. Which means they waste FPS by ALWAYS flashing an "empty" flash-frame container whenever their GUI is open.
    -- * There can sometimes be incorrect "ghost flash" frames if you do things such as the following sequence of events: Open spellbook ("P"), close the
    --   spellbook again, learn a spell (which marks the tab as "flash" since their code sees that their current "bookType" is SPELLBOOK), then open the
    --   Pet book directly ("Shift-I"). Their OnShow code will see that SOMETHING needs to be flashed, and will show an ugly "ghost flashing" frame.
    -- * Even WHEN Blizzard's spellbook SUCCESSFULLY flashes a tab, it's stupidly programmed to stop flashing after 30 seconds, which means that you
    --   could look away from the screen or think about something, and then when you look back at the spellbook it won't be flashing anymore; ugh.
    --
    -- NOTE: By post-hooking "OnShow", we're certain that their frame is visible and has applied its own (terrible) attempt at flashing, and is ready
    -- for us to sync the TinyBook tab state instead. And yes, the fact that we hook "OnShow" means we run this pointlessly during the brief visibility
    -- of Blizzard's spellbook during our "ToggleSpellBook" post-hook. But the CPU impact of that is laughably small, so it doesn't matter.
    -- NOTE: We don't need to do anything "OnHide", since their code always turns off all of their flash-frames and the flash-container.
    hooksecurefunc("SpellBookFrame_OnShow", function()
        TSB_SkillLineFlash("synctoblizzard");
    end);

    -- We already synchronize clicks on our TinyBook tabs (via "TSB_SpellBookSkillLineTab_OnClick") to stop flashing in the Blizzard spellbook too,
    -- but we'll also have to set up this "reverse sync", where any Blizzard clicks will turn off the TinyBook flashing for that tab and then re-sync.
    -- NOTE: We CANNOT hook their "SpellBookSkillLineTab_OnClick". Due to very poor coding by Blizzard, they've decided to programmatically call that
    -- function OnLoad and every OnShow, which means that we'd get false positives. Instead, we'll set PostClick handlers for the ACTUAL tab-buttons,
    -- which is great since the "PreClick/PostClick" handlers only trigger on actual mouse clicks (and "/click btn" macros and "btn:Click()" calls).
    -- NOTE: Due to the technique in "TSB_TinyBookToBlizzard" and "TSB_BlizzardToTinyBook", our active tab intentionally gets CLICKED when swapping
    -- view mode, which guarantees (bi-directionally) that the ACTIVE tab will stop flashing in both spellbooks whenever you change active view mode;
    -- that behavior makes the most sense, since you were viewing that tab in one of the Blizzard/TinyBook modes, so THAT TAB shouldn't keep flashing.
    for tabNum=1, MAX_SKILLLINE_TABS do -- Loop over all of Blizzard's tabs (note no "TSB_" prefix; we use Blizzard's variable this time).
        hookScript(_G["SpellBookSkillLineTab"..tabNum], "PostClick", function(self)
            -- NOTE: We DON'T proceed with handling this click if the Blizzard frame is HIDDEN and yet somehow got clicked (ie. via "/click" macros).
            -- NOTE: "GetChecked()" ensures that Blizzard's OnClick handler has accepted the click and made the tab "checked" (active).
            if (self:GetChecked() and SpellBookFrame:IsShown()) then
                local tinybookTabButton = _G["TSB_"..self:GetName()]; -- Adds "TSB_" prefix, to get TinyBook's equivalent button.
                if (tinybookTabButton) then
                    TSB_SkillLineFlash("stoptab", tinybookTabButton); -- Stop flashing that "spell school" tab in the TinyBook spellbook.
                    TSB_SkillLineFlash("synctoblizzard"); -- Sync all of TinyBook's flashing to Blizzard's spellbook, to ensure 1:1 accuracy.
                end
            end
        end);
    end
end

function TSB_SpellBookFrame_OnLoad(self)
    -- NOTE: This assignment is necessary for making the global into a local (see top of this file).
    TSB_SpellBookFrame = self;

    -- Inject some "quality of life" enhancements into Blizzard's spellbook, to bring it on-par with ours.
    TSB_EnhanceBlizzardSpellbook();

    -- Register Events.
    -- NOTE: We'll keep these events registered even when the frame is hidden. And our TSB_EventQueue system queues
    -- any in-combat events and safely fires them after combat ends instead.
    self:RegisterEvent("SPELLS_CHANGED");
    self:RegisterEvent("LEARNED_SPELL_IN_TAB");

    -- Initialize spellbook state.
    self.bookType = BOOKTYPE_SPELL; -- Start in the player's spellbook (not the pet spellbook).
    self.selectedSkillLine = 1; -- Start with the "General" spell school.

    -- Initialize ourselves to the first page of each "school" tab (right side) and the pet tab (bottom side).
    -- NOTE: We technically DON'T have to do this, since "TSB_SpellBook_[Get/Set]CurrentPage" both auto-write a 1 if the field is missing.
    for tabNum=1, TSB_MAX_SKILLLINE_TABS do
        TSB_SPELLBOOK_PAGENUMBERS[tabNum] = 1;
    end
    TSB_SPELLBOOK_PAGENUMBERS[BOOKTYPE_PET] = 1;

    -- Keep track of which order our bottom-tabs appear in.
    TSB_FRAME_TAB_LIST[BOOKTYPE_SPELL] = 1;
    TSB_FRAME_TAB_LIST[BOOKTYPE_PET] = 2;

    -- Initialize bottom-tab properties that will never change.
    -- NOTE: The TEXT of Tab 2 (the pet tab) is updated later, in "TSB_SpellBookFrame_Update", based on what pet you own!
    TSB_SpellBookFrameTabButton1.bookType = BOOKTYPE_SPELL;
    TSB_SpellBookFrameTabButton1:SetText(SPELLBOOK); -- NOTE: "SPELLBOOK" is a global string: "Spellbook".
    TSB_SpellBookFrameTabButton1.binding = "TOGGLESPELLBOOK";
    TSB_SpellBookFrameTabButton2.bookType = BOOKTYPE_PET;
    TSB_SpellBookFrameTabButton2.binding = "TOGGLEPETBOOK";

    -- Do an initial (hidden) update of the whole spellbook GUI.
    -- NOTE: We don't REALLY need to perform the "update" here, but it's rapid and ensures our initial GUI state is correct even while hidden.
    TSB_SpellBookFrame_Update(false); -- FALSE = Don't force SpellButton updates.

    -- Register intelligent API hooks, to closely integrate TinyBook into the default game GUI.
    --
    -- The ONLY code in the game which is able to call Blizzard's "ToggleSpellBook" is their OWN code. Any 3rd party calls to it
    -- would taint the execution path and make the spellbook unable to cast any spells. So we only have to worry about hooking
    -- Blizzard's official calls to the function. The full list is as follows, as well as our hooking strategies for each of them:
    --
    -- * Function calls which we will hook completely and redirect to our addon instead:
    -- - Keyboard bindings ("TOGGLESPELLBOOK" and "TOGGLEPETBOOK"), on P and Shift-I by default.
    -- - The Microbar "Spellbook" button.
    --
    -- * Function calls which we will ALLOW to proceed as usual (we'll still hook them, but won't make our frame appear):
    -- - Their three "SpellBookFrameTabButton" bottom-tabs in Blizzard's book, which switch between viewing "Spellbook" or "Pet".

    -- Register Pre-Click handlers on Blizzard's spellbook bottom-tabs, which tell us to ALLOW the next "ToggleSpellBook" API (used by those buttons).
    -- NOTE: If we don't do this, using the regular spellbook's bottom-tabs would CLOSE Blizzard's spellbook and take us (via hook) to TinyBook instead!
    -- NOTE: Thanks to being a separate Pre-Click handler (rather than OnClick), these code injections do NOT cause any execution taint! Phew.
    for i=1, 3 do
        hookScript(_G["SpellBookFrameTabButton"..i], "PreClick", function() TSB_AllowNextBlizzardSpellBook(); end);
    end

    -- Also register a very subtle Pre-Click handler for the "Spellbook" MicroBar button...
    -- NOTE: This solves one extremely specific, very tiny issue... The fact that if you press the microbar button, it should
    -- do one of three things: 1) If nothing is open then open the "Spellbook", 2) if "Spellbook" is open then close the spellbook,
    -- or 3) if "Pet" is open then switch back to "Spellbook" instead. However, if the user had switched from TinyBook to Regular
    -- spellbook GUI, the button worked properly regarding CLOSING the Blizzard window (thanks to our "ToggleSpellBook" hook
    -- being smart enough to understand when the API is used for closing the Blizzard window), but it DIDN'T work properly when
    -- the user was viewing the Blizzard window's "Pet" tab. If so, a click would WRONGLY close the BLIZZARD "Pet" book and open
    -- the TINYBOOK "Spellbook" instead(!). This tiny change below now ensures that if Blizzard's window is open, we tell our hook
    -- to NOT interfere with the next API call, which in turn ensures that going from "Pet" to "Spellbook" via microbar in Blizzard
    -- mode works properly. (And of course, ALL these microbar actions work perfectly when the "TinyBook" window is the active GUI!)
    -- NOTE: We CANNOT solve the SAME problem when the user presses the KEYBOARD keys (such as P for Spellbook or Shift-I for Pet);
    -- in that case, pressing the same button as the currently-viewed tab WILL PROPERLY close the Blizzard spellbook; but pressing
    -- the OTHER button (going from Pet to Spellbook, or vice versa), will switch to the CORRECT tab BUT will use the TinyBook GUI
    -- instead. However, that scenario is WAY too complex (and rare) to bother "fixing", since it would be hell to make the post-hook
    -- understand the "bottom-tab-switching within Blizzard spellbook via KEYBOARD" scenario. And besides, most players don't even
    -- know that Shift-I for "Pet" exists as a shortcut. They only use "P" for "Spellbook" and won't notice anything!
    hookScript(SpellbookMicroButton, "PreClick", function()
        if (SpellBookFrame:IsShown()) then TSB_AllowNextBlizzardSpellBook(); end
    end);

    -- When hooking, we want to SILENCE Blizzard's spellbook "Open" sound; otherwise EVERY hooked "ToggleSpellBook" call
    -- would be preceded with THEIR "Opening" sound EVEN WHEN the hooked call results in CLOSING our TinyBook window,
    -- since every call FIRST opens (or closes, in some cases) the Blizzard spellbook BEFORE we take over the call (below).
    --
    -- However, getting rid of the sound ISN'T straight-forward. We must disable SoundFX BEFORE Blizzard's code runs PlaySound,
    -- which it does in its "SpellBookFrame_Update" function, which in turn gets called by the sequence of actions in
    -- Blizzard's "ToggleSpellBook" function. But we CANNOT PRE-HOOK "ToggleSpellBook", so the best thing we can do is to
    -- intelligently post-hook a "silencing" handler WITHIN one of the INNER function-calls inside of their "ToggleSpellBook"
    -- code, but BEFORE any of their other calls that play sounds. This actually proved itself to be MUCH harder than expected,
    -- because their inner code doesn't execute in the order that you'd expect. The functions are listed in a simple order:
    -- "HideUIPanel, ShowUIPanel, UpdatePages", but the ACTUAL call order (due to various event handler callbacks),
    -- is "HideUIPanel", "SpellBookFrame_UpdatePages, SpellBookFrame_Update" (those two are repeated as a pair 3 times),
    -- "ShowUIPanel", "SpellBookFrame_UpdatePages", and then finally our code post-hook for "ToggleSpellBook", and then the
    -- next frame's "OnUpdate" after that (which proves the weird call-order above ISN'T due to deferred "next frame" handling).
    --
    -- The final solution is to post-hook "HideUIPanel", which ALWAYS runs in ToggleSpellBook, and disable sound effects
    -- there, and then not re-enabling sound effects until our "ToggleSpellBook" post-hook runs. This perfectly silences
    -- the "opening" sound, while leaving the "closing" sound alone! Because we WANT Blizzard's closing sound to play when
    -- THEY close it via ToggleSpellBook (in the cases where the user is viewing Blizzard's spellbook manually and then
    -- closes it; just so that we don't want to have to re-implement their closing sound too).
    --
    -- Furthermore, we'll use the "HideUIPanel" hook to ALSO CLOSE our TinyBook window (if it was open), to ensure that Blizzard's
    -- "UI Panels" system never has to make room for two spellbooks side by side. If we didn't close ours, and ours was open
    -- while Blizzard's spellbook call happened, then the game would have to make room for TWO spellbook panels, and would
    -- sometimes be forced to close something else to make room. That's not good. So instead, we'll do a clean hook where we
    -- ALSO hide OUR OWN frame, so that IF their "ToggleSpellBook" code decides to open their spellbook panel, then at least
    -- we've already closed ours, to ensure the user doesn't run out of "panel" space (at most 3 panels can be open on-screen).
    --
    -- And yes, this matters. For an example of the problem/risks of multiple frames, try opening the character panel ("C") and
    -- the dressing room window (by ctrl-clicking on any item), then press "P" (spellbook) and then finally "Shift-I" (pet book).
    -- The result is that when you press "P", the Blizzard spellbook opens, and is immediately hidden, and then ours opens. So
    -- far so good, but when you finally press "Shift-I" to "switch from spellbook to pet tab", the Blizzard spellbook is what
    -- opens first (via "ToggleSpellBook" on the keyboard), WHILE our TinyBook frame is also open. And since we were already
    -- at the panel-limit (3 panels: TinyBook, Character, and Dressing Room), the leftmost panel (in this case, TinyBook),
    -- is forcibly closed, and THEN the Blizzard panel opens. After that, our "ToggleSpellBook" post-hook runs and closes the
    -- Blizzard frame and opens ours on the desired page. This all happens so quickly that the user won't notice much except
    -- that they may lose some panel that would otherwise have fit, and that they also won't hear the expected "close spellbok"
    -- sound before the "open pet book" sound plays (due to our muting that happens in Blizzard's "ToggleSpellBook" code, where
    -- we mute the sound BEFORE they call ShowUIPanel which displaces (and forcibly closes) our TinyBook panel). But that "using
    -- keyboard controls to CHANGE spellbook tabs" is actually the ONLY scenario where this problem can occur, since we are very
    -- diligent about first CLOSING frames BEFORE opening in all other code paths. However, by simply ensuring that we ALSO hide
    -- OUR frame via the "HideUIPanel" hook below, we can COMPLETELY ELIMINATE the issue even for keyboard-controlled swapping,
    -- since we'll ENSURE that only ONE spellbook panel can EVER be in the "shown" state at a time. Perfect!
    --
    -- So, here's the sequence of actions: First, "ToggleSpellBook" runs, then it executes "HideUIPanel", which runs their
    -- OnHide handler which plays the "closing spellbook" sound (but only IF their book WAS visible). Then our post-hook
    -- for "HideUIPanel" runs and hides OUR SPELLBOOK (which plays the "closing spellbook" sound, IF ours was visible),
    -- and then it turns off all soundfx (which doesn't mute the game or ongoing sounds; it just prevents further calls to
    -- PlaySound/PlaySoundFile from playing anything). Then control returns to their ToggleSpellBook code which POSSIBLY
    -- (depending on current GUI state) will run "ShowUIPanel", which makes their spellbook visible and runs a bunch of code
    -- which includes some PlaySound calls (which we've silenced), and finally their code runs the "update pages" function.
    -- All of this means that we've successfully allowed their/our "close" sounds but muted their "open" sound. After that,
    -- our "ToggleSpellBook" post-hook runs and restores the user's desired sound setting again. To make this process
    -- perfect, we'll simply have to re-implement the standard "spellbook opening" sound in our post-hook in the scenario
    -- where we ALLOW Blizzard's spellbook to open, to ensure that we hear the opening sound when it's ACTUALLY needed!
    --
    -- All of this work just to avoid dual UI Panels or "double sound effects" playing, hehe... but it's TOTALLY worth it! ;-)
    --
    -- NOTE: This code is designed so that if the "HideUIPanel" hook never runs, the "ToggleSpellBook" hook will still run
    -- perfectly, but you'll hear the "double sound effects" issue and there's the risk of overcrowded (auto-closing) UI panels.
    local restoreEnableSFX, wasTinyBookShown;
    hooksecurefunc("HideUIPanel", function(frame)
        -- If the target isn't Blizzard's SpellBookFrame, then we can immediately quit here and not waste CPU checking the stack.
        if (frame ~= SpellBookFrame) then return; end
        -- Now we must make sure that this call is happening INSIDE of "ToggleSpellBook" in Blizzard's SpellBookFrame.lua.
        -- To detect that, we'll look for the stack signatures of their code file and function name, which are as follows:
        -- "in function <Interface\FrameXML\SpellBookFrame.lua:9>" and "in function `ToggleSpellBook'" (note the special left-quote).
        -- NOTE: The official Blizzard code only runs "HideUIPanel(SpellBookFrame)" from two places; in "ToggleSpellBook" and also
        -- in "SpellBookFrame_Update" (but only in the rare scenario where the user is viewing the Pet tab and then loses their pet).
        -- We also run it a FEW times during our hooking (when we intercept the API call). So this stack scan doesn't run often!
        local callStack = debugstack();
        if (callStack:find([[<Interface\FrameXML\SpellBookFrame.lua:]]) and callStack:find("[`']ToggleSpellBook'")) then
            -- Ensure that our spellbook is closed (since Blizzard's will most likely open), so we don't encounter UIPanel space issues.
            wasTinyBookShown = TSB_SpellBookFrame:IsShown();
            if (wasTinyBookShown) then
                HideUIPanel(TSB_SpellBookFrame); -- Allowed to play its sound, since a visible panel means we WANTED to "toggle" (close) it!
            end

            -- Silence... shhhhh... This prevents the Blizzard spellbook from playing its "opening sound".
            restoreEnableSFX = GetCVar("Sound_EnableSFX");
            SetCVar("Sound_EnableSFX", 0);
        end
    end);

    -- Hook Blizzard's "toggle spellbook" API and intelligently decide what to do with each API call.
    -- NOTE: This API is how we'll be able to inject and "redirect" keyboard control and microbar clicks to our TinyBook GUI instead.
    -- NOTE: We use a safe post-hook to avoid tainting Blizzard's secure "ToggleSpellBook" function. If we didn't do that, and instead
    -- tried to overwrite/modify their function, we'd actually taint the Blizzard spellbook completely and make it unable to cast spells!
    hooksecurefunc("ToggleSpellBook", function(bookType)
        --[[ COMMENTED OUT BECAUSE IT HAS NO USE NOW, BUT MAY BE VERY USEFUL SOME OTHER TIME:
        -- Detect whether "ToggleSpellBook" was called via the keyboard bindings or from a click somewhere.
        -- NOTE: This inspects the ENTIRE call-stack, which means that even if the call to "ToggleSpellBook" was hidden
        -- through many levels of function calls, we'll still properly detect where the execution began.
        -- NOTE: Click handlers are marked as "*:OnClick" (without button-name info) in the call-stack text, whereas executions that began from
        -- the keyboard bindings are marked as "[string "TOGGLESPELLBOOK"]:1: in function <[string "TOGGLESPELLBOOK"]:1>" (or TOGGLEPETBOOK).
        local callStack = debugstack();
        --print('---'); for s in callStack:gmatch("[^\r\n]+") do print('>>'..s); end print('---'); -- Easy inspection of stack contents.
        --local clickCall = callStack:find(":OnClick"); -- Alternative: Detects if this was called from an OnClick handler (but cannot know WHICH button).
        local bindingCall = callStack:match('%[string "(TOGGLE[A-Z]+BOOK)"%]');
        if (bindingCall ~= "TOGGLESPELLBOOK" and bindingCall ~= "TOGGLEPETBOOK") then
            bindingCall = nil;
        end
        ]]

        -- Check current frame visibility status.
        -- NOTE: Since our hook runs after Blizzard's API call has already executed the default Blizzard code, their frame is already
        -- in its finished state (visible or hidden), whereas OUR frame state here is just in its pre-toggle state. Be aware of that!
        -- NOTE: If "isBlizzardShown" is negative, it means their frame WAS visible and got closed by the current API call!
        -- NOTE: For "isTinyBookShown", we use the PRE-CLOSING/PRE-TOGGLING value from our "HideUIPanel" hook above, before we hid the panel.
        local isBlizzardShown = SpellBookFrame:IsShown();
        local isTinyBookShown = wasTinyBookShown; -- Instead of "TSB_SpellBookFrame:IsShown();", since we're ALWAYS hidden after "HideUIPanel" hook.
        --print("B:"..tostring(isBlizzardShown)..", T:"..tostring(TSB_SpellBookFrame:IsShown())..", wasT:"..tostring(wasTinyBookShown)); -- "T" should always be nil here.

        -- If the "restore sfx" flag is non-nil, it means that sound was turned off by our "HideUIPanel" hook above, so we'll restore it.
        -- NOTE: As mentioned in the lengthy comments for the hook above, the only sound we've muted is their "open" sound (not their/our "close" sounds).
        if (restoreEnableSFX) then
            SetCVar("Sound_EnableSFX", restoreEnableSFX);
            restoreEnableSFX = nil;
        end

        -- Determine which spellbook we should use. If we're in combat lockdown, we actually MUST use Blizzard's instead.
        -- NOTE: We'll use Blizzard's handler if we're marked as "must allow next API call", or if we're in combat, or if Blizzard's
        -- frame is now **ALREADY CLOSED** which means that it WAS OPEN but then got hidden by the current API call. Because if the API
        -- call closed Blizzard's frame, it means the user WAS viewing Blizzard's frame and then pushed a key/button to toggle (hide)
        -- it, so in that case we definitely shouldn't immediately open ours (that'd be annoying as hell).
        if (allowNextBlizzardSpellBook or TSB_CombatLockdown.inCombat or (not isBlizzardShown)) then -- Use Blizzard's spellbook/API handler.
            -- Using Blizzard's spellbook is simple: We don't open ours, and just accept Blizzard's handling of this "ToggleSpellBook" call!

            -- If we're in combat and we've now opened the Blizzard frame, tell the user WHY Blizzard's opened!
            if ((not allowNextBlizzardSpellBook) and TSB_CombatLockdown.inCombat and isBlizzardShown) then
                print('Opening regular spellbook due to combat lockdown.');
            end

            -- Since our "HideUIPanel" hook silences the "opening" sound of Blizzard's spellbook, we'll have to play their sound now.
            -- NOTE: These sound names are taken from "SpellBookFrame_Update" and represent the "Spellbook" and "Pet" tabs. However,
            -- they actually sound identical ingame (both sound files are indistinguishable), but that's how Blizzard designed it. ;-)
            if (isBlizzardShown) then
                PlaySound(SpellBookFrame.bookType == BOOKTYPE_SPELL and "igSpellBookOpen" or "igAbilityOpen");
            end

            -- Disable our internal "allow next attempt to open Blizzard spellbook" and "re-open TinyBook after combat" flags.
            -- NOTE: The reason for disabling "automatic re-open" is that it would be confusing for users if they view TinyBook, then
            -- enter combat (which automatically closes the TinyBook frame), and then they manually open Blizzard's spellbook in combat,
            -- navigate around a bit and do what they need to do, and yet after the combat their screen would STILL get peppered with
            -- the TinyBook GUI too (which they most likely no longer need, since they've used Blizzard's). That'd be annoying!
            allowNextBlizzardSpellBook = false;
            TSB_SpellBookFrame.reopenAfterCombat = false;

            -- Now ENSURE that TinyBook's GUI is hidden (if it SOMEHOW wasn't already), since they want the Blizzard frame to handle everything.
            -- NOTE: Thanks to our "HideUIPanel" hook above, the frame will/should always be hidden already, but it's here as a failsafe just in case.
            if (TSB_SpellBookFrame:IsShown()) then
                -- NOTE: We DON'T "doSilently()", since we WANT our "close spellbook" sound to play simultaneously as their frame appears,
                -- exactly like when you switch between the REGULAR bottom-tabs ("Spellbook" or "Pet") of Blizzard's (and our) spellbook.
                HideUIPanel(TSB_SpellBookFrame);
            end
        else -- Use TinyBook spellbook.
            -- We want the TinyBook GUI, so simply redirect the "toggle" action to our addon (to show/hide it), and ensure Blizzard's is hidden.

            -- Hide Blizzard's regular book immediately. Prevents it from appearing on-screen.
            -- NOTE: Our post-hook is executing BEFORE Blizzard's spellbook GUI has been drawn on-screen (great!), but we'd still HEAR the closing
            -- of the frame. So to make our integration perfectly seamless, we'll silence the "closing spellbook" sound from Blizzard's spellbook.
            doSilently(function()
                HideUIPanel(SpellBookFrame);
            end);

            -- Toggle (open or close) our TinyBook GUI.
            -- NOTE: We allow this to play its opening or closing sound, exactly as intended.
            -- NOTE: Our "closing" was ACTUALLY done in our "HideUIPanel" hook above, which forcibly closes TinyBook's GUI too. So we'll tell
            -- "TSB_ToggleSpellBook" about that PREVIOUS "visibility" state via its optional second parameter, so that it will ONLY OPEN the
            -- spellbook IF it WASN'T open (or was on another book type tab, which also qualifies us for immediately re-opening the spellbook).
            -- Otherwise we'd never be able to close it (it'd always re-open here, since the frame is always invisible here at this moment)...
            TSB_ToggleSpellBook(bookType, isTinyBookShown);
        end
    end);

    -- Register combat lockdown handler, and set up initial "reopen after combat" state.
    self.reopenAfterCombat = false;
    TSB_CombatLockdown:registerCallback("HandleCombatLockdown", TSB_HandleCombatLockdown);
end

function TSB_SpellBookFrame_OnEvent(self, event, ...)
    -- If the GUI is in combat lockdown, save the event in a queue for later processing instead...
    -- NOTE: We actually allow a very specific exception for "LEARNED_SPELL_IN_TAB", because ALL of the functions calls that it performs
    -- are usable in combat, and it's an IMPORTANT event which is responsible for syncing the "spell school flashing" state to Blizzard's
    -- spellbook too. So if the player is in combat and is viewing the Blizzard frame and learns a spell (somehow) in combat, we'll update
    -- their GUI properly (and instantly) by allowing this event to get through immediately, rather than becoming queued until combat ends.
    if (TSB_CombatLockdown.inCombat and event ~= "LEARNED_SPELL_IN_TAB") then
        TSB_EventQueue:addEvent(TSB_SpellBookFrame_OnEvent, self, event, ...);
        return;
    end

    local arg1 = ...; -- Extract relevant args from varargs.
    if (event == "SPELLS_CHANGED") then
        -- This event covers ALL important spell list changes: It fires whenever the player gains or loses ANY spell/profession/ability (or rank),
        -- INCLUDING gaining/losing a pet (which counts as gaining or losing ITS abilities). In fact, it even triggers for gaining/losing pets
        -- with ZERO spells. Which means that this event is perfect for detecting all spell list changes AND all pet changes. And it's important
        -- that we do a "full GUI update" whenever this event fires; otherwise we'd get a corrupted spell list if the player gains or loses spells
        -- while our spellbook is open, since all of WoW's internal "spell ID offsets" CHANGE after this event and would no longer match our GUI state.

        -- Regardless of our frame's visibility: Ensure that the spell "flyout" window is closed and FORGETS about its active IDs, since the spell
        -- list (and therefore ID offsets) have potentially changed now. If we don't clear the list, our flyout may show the wrong spell IDs!
        -- NOTE: This DOES mean that we'll also hide-and forget every time Blizzard's spellbook briefly appears before our "P"-key hook takes over,
        -- since their spellbook fires "SPELLS_CHANGED" on opening and EVERY navigation. And OUR spellbook ALSO fires it on opening (but not navigation);
        -- but either way, it's super important to clear the cache when spells have TRULY changed, and re-configuring the flyout is fast and trivial.
        TSB_RankViewer_CloseAndForget();

        -- NOTE: We only want to update our GUI if our frame is VISIBLE, because Blizzard's spellbook is poorly programmed and constantly
        -- calls "UpdateSpells()" which in turn fires "SPELLS_CHANGED". That happens for pretty much ALL navigation actions in THEIR spellbook,
        -- including the mere act of opening the spellbook. And since our keyboard post-hook FIRST opens Blizzard's frame, we REALLY need to be
        -- sure that we don't react to that event. It'd just cause pointless extra processing for us. We only care when WE'RE visible, in which
        -- case the event MAY signal a super important change to the spell list or player's pet. And even IF something truly important happens
        -- to be ignored while we are INVISIBLE, we actually ALWAYS refresh the WHOLE GUI state OnShow when our spellbook becomes visible again!
        if (TSB_SpellBookFrame:IsShown()) then
            -- Spells were changed while GUI is open. We MUST now update the entire GUI state (including the current page's content).
            -- NOTE: If we HAD a pet and WERE viewing the PET PAGE, and then dismiss the pet, this will now show us an empty spell list.
            TSB_SpellBookFrame_Update(true); -- True = Force spell buttons to update themselves.

            -- The NORMAL Blizzard spellbook auto-closes if the player is viewing "Pet" spells and then loses their pet. We'll instead
            -- keep the book open, but will switch back to regular spells. IF we DON'T do this switch here, the user would actually be
            -- stuck with the totally empty frame (no pet spells anymore, and hidden bottom-tabs).
            -- NOTE: This trick will take the user back to their last-viewed "regular spell school" AND page number! :-)
            local hasPet = HasPetSpells(); -- Check if we have a pet or not.
            if ((not hasPet) and TSB_SpellBookFrame.bookType == BOOKTYPE_PET) then
                TSB_ToggleSpellBook(BOOKTYPE_SPELL); -- View regular spells instead.
            end
        else
            -- If we're invisible, then this event was MOST LIKELY triggered by Blizzard's spellbook. But there IS a small chance that it happened
            -- due to the player gaining or losing a pet, so we MAY need to reposition the "Switch between Blizzard/TinyBook spellbook"-tabs.
            -- NOTE: If we're visible (above) instead, "TSB_SpellBookFrame_Update" takes care of calling this function internally.
            TSB_RePosition_FrameTab4();
        end
    elseif (event == "LEARNED_SPELL_IN_TAB") then -- (Allowed to execute even in combat. All API calls below must be usable in combat.)
        -- When a new spell (or higher rank) is learned, start flashing the spellbook tab (or queue it up if the spellbook is hidden/viewing "pet").
        -- NOTE: arg1 = Number of the "spell school" tab where the spell/ability was added. Indexed as 1 (general tab), 2 (next tab after that), etc...
        -- NOTE: Unlike Blizzard's spellbook code, we actually queue up the flashing EVEN IF we're on the Pet tab.
        TSB_SkillLineFlash("queue", arg1);

        -- Start flashing IMMEDIATELY if the spellbook is already open.
        -- NOTE: This is something that the original Blizzard spellbook never did, which meant that its flashing-state was "lost" if your spellbook
        -- was open while you learned a skill, since closing and re-opening the Blizzard spellbook clears ALL queued flashing OnHide, which meant
        -- that flashing gets BUGGED and LOST in Blizzard's spellbook. That's one of many reasons why Blizzard's "spellbook flashing" is so weird
        -- and finicky and easily gets lost (and there are other reasons too). This technique fixes it, by flashing immediately if visible.
        -- NOTE: We'll start flashing ANY tab even if the user is ALREADY viewing that tab. That's how the spellbook works OnShow too!
        TSB_SkillLineFlash("start");

        -- Sync our perfect skill-line flashing state to Blizzard's spellbook. But only if they're visible (there's no point if they are hidden).
        -- NOTE: Since we listen to this event EVEN while our own frame is invisible, this actually means that we'll ALSO fix Blizzard's frame
        -- if their frame is the ONLY visible one. And we actually NEED to do the syncing HERE in OUR event handler; we CAN'T do it by post-hooking
        -- their own "OnEvent" since their handler (registered earlier) runs BEFORE ours, so our flash frame state wouldn't be correct at that time.
        if (SpellBookFrame:IsShown()) then
            TSB_SkillLineFlash("synctoblizzard");
        end
    end
end

function TSB_SpellBookFrame_OnShow(self)
    -- If the GUI is in combat lockdown, we aren't allowed to update the GUI state and spells etc, so just immediately close ourselves again.
    -- NOTE: None of our normal code paths EVER open this frame in combat. This simply protects against MANUALLY called "ShowUIPanel(TSB_SpellBookFrame)"
    -- or "TSB_ToggleSpellBook()" executions. Also note that ONLY "ShowUIPanel"-based calls work; "TSB_SpellBookFrame:Show()" is actually 100% ignored
    -- by BLIZZARD in combat. And most "tinkering" users (misguided people who may try opening in combat) use ":Show", so they won't even get this far.
    if (TSB_CombatLockdown.inCombat) then
        doSilently(function()
            HideUIPanel(TSB_SpellBookFrame); -- Silently closes our frame again.
        end);
        print("The TinyBook interface cannot be opened in combat."); -- Normal users will NEVER see this message!
        return;
    end

    -- Update the entire GUI state (including the current page's content), and play "open" sound.
    -- NOTE: We achieve this by triggering the "UpdateSpells()" API, which tells the game to ENSURE that the entire spellbook is loaded into
    -- the client, and then it IMMEDIATELY fires the "SPELLS_CHANGED" event, which our OnEvent listener handles and does a full GUI update/reset!
    -- NOTE: We'll be doing this OnShow every time the GUI opens AND when they switch between Spellbook/Pet tabs (which closes and re-opens the GUI).
    UpdateSpells(); -- NOTE: Instantly (synchronously) triggers "SPELLS_CHANGED" (and therefore our OnEvent) BEFORE returning back here.
    PlaySound("igSpellBookOpen");

    -- If there are tabs waiting to flash, then flash them...
    TSB_SkillLineFlash("start");

    -- Show multibar slots... Update: Actually, no...
    -- NOTE: Blizzard's spellbook calls MultiActionBar_ShowAllGrids() and HideAllGrids()
    -- to show all action bar slots even when nothing exists in those slots (even when
    -- the user has "Always Show ActionBars" unchecked in their game options). It does
    -- that on spellbook-open and on close. However, that function ISN'T CALLABLE from
    -- 3rd party addons and does nothing if we try it (not even if manually typed "/run").
    -- So we won't call it here (or OnHide). It's no big problem, because as soon as the
    -- user picks up and drags a spell, the game automatically renders all bars anyway,
    -- exactly as intended. So they don't lose any important functionality!
    --MultiActionBar_ShowAllGrids();
    TSB_UpdateMicroButtons();
end

function TSB_SpellBookFrame_OnHide(self)
    -- Play "close" sound, update microbar button state, and hide the spell school "flashing" container.
    -- NOTE: All of the function calls below can be done in combat, so there's no danger hiding this frame AFTER combat has already started.
    if (TSB_SpellBookFrame.bookType == BOOKTYPE_SPELL) then
        PlaySound("igSpellBookClose"); -- Normal book sound.
    else
        PlaySound("igAbilityClose"); -- Pet book sound.
    end
    TSB_UpdateMicroButtons();
    TSB_SkillLineFlash("hidecontainer"); -- NOTE: Doesn't stop the buttons themselves. They'll flash again on re-open.

    -- Hide multibar slots... Update: Actually, no...
    -- NOTE: See "TSB_SpellBookFrame_OnShow" comment for why we cannot call this function!
    --MultiActionBar_HideAllGrids();
end

function TSB_UpdateMicroButtons()
    -- Toggle the SpellBook's MicroBar button between "pushed" and "normal" states, to indicate whether ANY spellbook (ours or Blizzard's) is open.
    -- NOTE: This performs the only RELEVANT subset of what Blizzard's official "UpdateMicroButtons()" does (which is called by Blizzard's spellbook).
    -- NOTE: We ARE affecting a secure Blizzard frame here... but it THANKFULLY doesn't get tainted by us touching its button state!
    -- NOTE: It's possible to edit this property while in combat.
    if (TSB_SpellBookFrame:IsShown() or SpellBookFrame:IsShown()) then
        SpellbookMicroButton:SetButtonState("PUSHED", 1);
    else
        SpellbookMicroButton:SetButtonState("NORMAL");
    end
end

------
-- Page Switching
------

function TSB_ChangePageButton_OnClick(self, offset)
    PlaySound("igAbiliityPageTurn");

    -- Change page based on the direction of the button.
    TSB_SpellBook_SetCurrentPage(offset);

    -- Load the currently selected page's contents.
    -- NOTE: We don't need to run the whole "Update" here (our GUI is already fine); just "UpdatePage" is enough.
    TSB_SpellBookFrame_UpdatePage(true); -- True = Force spell buttons to update themselves.
end

function TSB_SpellBook_SetCurrentPage(offset)
    -- Apply the desired navigation offset, and clamp it to the legal page range.
    assert(type(offset) == "number", "Bad argument #1 to 'TSB_SpellBook_SetCurrentPage' (number expected)");
    local currentPage, maxPage = TSB_SpellBook_GetCurrentPage();
    local pageKey = (TSB_SpellBookFrame.bookType == BOOKTYPE_PET) and BOOKTYPE_PET or TSB_SpellBookFrame.selectedSkillLine;
    currentPage = currentPage + offset; -- Offset is either +1 or -1.
    if (currentPage < 1) then
        currentPage = 1; -- Never allow navigation before the 1st page.
    elseif (currentPage > maxPage) then -- NOTE: maxPage is always 1 or higher, so "elseif" is safe.
        -- NOTE: Blizzard does a SIMILAR "if current over max" check in their "SpellBookFrame_UpdatePages" function, but they actually have
        -- a huge bug in that they READ from the proper "pageKey" but ALWAYS write to the NON-PET "selectedSkillLine" pageKey. Haha. ;-)
        currentPage = maxPage; -- Never allow navigation beyond the final page.
    end
    TSB_SPELLBOOK_PAGENUMBERS[pageKey] = currentPage;
    return currentPage, maxPage;
end

function TSB_SpellBook_GetCurrentPage()
    -- Calculate current and maximum page numbers for the active book and "spell school" tab.
    local currentPage, maxPage;
    local pageKey = (TSB_SpellBookFrame.bookType == BOOKTYPE_PET) and BOOKTYPE_PET or TSB_SpellBookFrame.selectedSkillLine;
    currentPage = TSB_SPELLBOOK_PAGENUMBERS[pageKey];
    maxPage = ceil(SPELL_ID_LIST_COUNT/TSB_SPELLS_PER_PAGE);
    if (type(currentPage) ~= "number" or currentPage < 1) then
        -- NOTE: This is just extra "protection" against MANUALLY written bad/missing values (never happens via "TSB_SpellBook_SetCurrentPage").
        currentPage = 1;
        TSB_SPELLBOOK_PAGENUMBERS[pageKey] = currentPage;
    end
    if (maxPage < 1) then
        -- We must always offer "Page 1" even in an empty spellbook, so that pagination works properly ("Page 1 of 0" makes no sense).
        -- NOTE: Blizzard's code DOESN'T do this, and their pagination code totally breaks if a "spell school" tab is ever empty.
        maxPage = 1;
    end
    if (currentPage > maxPage) then
        -- NOTE: Yet another layer of "protection" against MANUALLY written bad values, which never happens via official code.
        currentPage = maxPage;
        TSB_SPELLBOOK_PAGENUMBERS[pageKey] = currentPage;
    end
    return currentPage, maxPage;
end

------
-- "Spell School" Tabs
------

function TSB_SpellBookSkillLineTab_OnClick(self)
    local tabId = self:GetID();

    -- Uncheck previously selected tab, and then check the clicked tab.
    -- NOTE: Since our GUI is already in a perfectly organized state at this moment, this method is much more efficient than running the
    -- whole "TSB_SpellBookFrame_UpdateSkillTabs" (which loops through ALL tabs and unchecks all non-selected and checks the selected tab).
    _G["TSB_SpellBookSkillLineTab"..TSB_SpellBookFrame.selectedSkillLine]:SetChecked(nil);
    self:SetChecked(1);

    -- Switch the active "spell school" tab, and then re-render the list of spells.
    -- NOTE: We don't need to run the whole "Update" here (our GUI is already fine); just "UpdatePage" is enough.
    TSB_SpellBookFrame.selectedSkillLine = tabId;
    TSB_SpellBookFrame_UpdatePage(true); -- True = Force spell buttons to update themselves.

    -- Stop flashing the clicked tab (if it was flashing due to new/changed spells).
    -- NOTE: We don't stop ALL flashing here, since there can be multiple flashing tabs at once. We just stop the CLICKED tab!
    TSB_SkillLineFlash("stoptab", self);

    -- Ensure that Blizzard's spellbook is also updated if it's SOMEHOW appearing side-by-side with ours.
    if (SpellBookFrame:IsShown()) then
        TSB_SkillLineFlash("synctoblizzard");
    end

    -- Play a sound to notify the user that they've switched spell-school.
    -- NOTE: The regular Blizzard spellbook doesn't play any sound at all when switching school tabs, so we'll be tasteful
    -- here and just play a "soft", non-distracting sound, which is SHORT. The length of the sound MATTERS since "PlaySound"
    -- refuses to play a sound again until the previous request for that exact sound has finished playing!
    -- NOTE: The "IsShown()" check is just here to silence ourselves if we programmatically call OnClick while the GUI is hidden.
    if (TSB_SpellBookFrame:IsShown()) then
        PlaySound("igMainMenuOptionCheckBoxOn"); -- Short, soft and gives nice feedback that a click happened. Perfect!
    end
end

-- Controls the "flashing" layer on top of the skill line buttons.
-- NOTE: This is a HUGE rewrite of Blizzard's buggy, simplistic, annoying "flashTabs" system. Ours is much more advanced and actually maintains
-- the "flashing" buttons BETWEEN re-openings of the spellbook. It no longer annoyingly clears all flashing every time you SNEEZE at the spellbook!
-- NOTE: Our "persistent flashing between re-openings" DOES have a slight hypothetical problem, but it's something that can NEVER happen in real
-- gameplay; and that's the fact that if you have 5 skill lines, and the 5th flashes, and then you're reduced to just having 4 skill lines (which
-- hides the 5th button but not its flash frame), then you'd see a ghost-flash on the 5th. However, this ISN'T an issue in actual usage since the
-- game ALWAYS has exactly 4 skill line tabs (General, and 3 "spell school" tabs). If the game ever begins using a different amount than 4 skill
-- lines, then it would be trivial to run some kinda "flash frame cleanup" step on an event; perhaps "SKILL_LINES_CHANGED" (sounds appropriate).
-- NOTE: All functions below (even syncing to Blizzard) can be done IN COMBAT, since all of the related frames and APIs are NON-SECURE code! Phew!
function TSB_SkillLineFlash(action, ...)
    if (action == "queue") then
        -- Queues up tab flashing to begin the next time "start" is called (or IMMEDIATELY if flash container is already active).
        -- NOTE: If OTHER tabs are already flashing (meaning flash container is active), then this will start flashing IMMEDIATELY without "start".
        local tabNum = ...; -- Takes the numeric index (1 to 8) of the tab to flash.
        if (type(tabNum) ~= "number" or tabNum < 1 or tabNum > TSB_MAX_SKILLLINE_TABS) then
            error(format("Bad argument #2 to 'TSB_SkillLineFlash'. Expected a number from 1 to %d.", TSB_MAX_SKILLLINE_TABS), 2);
        end
        local flashFrame = _G["TSB_SpellBookSkillLineTab"..tabNum.."Flash"];
        if (flashFrame) then
            flashFrame:Show();
        end
    elseif (action == "getflashtabs") then
        -- Gets a list of all active/queued flash tabs.
        local flashTabs = {};
        local flashFrame;
        for i=1, TSB_MAX_SKILLLINE_TABS do
            flashFrame = _G["TSB_SpellBookSkillLineTab"..i.."Flash"];
            if (flashFrame and flashFrame:IsShown()) then
                flashTabs[#flashTabs+1] = flashFrame;
            end
        end
        return flashTabs;
    elseif (action == "start") then
        -- Begins flashing if there are tabs waiting to flash.
        -- NOTE: We NEVER start flashing unless we are VISIBLE and on the SPELLBOOK tab; otherwise we'd see a ghostly flashing on the pet book!
        local flashTabs = TSB_SkillLineFlash("getflashtabs");
        if (TSB_SpellBookFrame:IsShown() and TSB_SpellBookFrame.bookType == BOOKTYPE_SPELL and #flashTabs > 0) then
            -- NOTE: This is safe to call multiple times. It simply ignores calls if already flashing a specific frame reference.
            -- NOTE: We use "-1" as duration (flash forever (until clicked to stop)), unlike Blizzard's spellbook code which uses "30" seconds.
            UIFrameFlash(TSB_SpellBookTabFlashFrame, 0.5, 0.5, -1, nil); -- NOTE: This also makes the frame visible if it was hidden.
        else
            TSB_SkillLineFlash("hidecontainer"); -- Ensure that the flash layer container frame is absolutely hidden.
        end
    elseif (action == "stoptab") then
        -- Takes a single tab button object and tells it to stop flashing. Does not affect any other tab buttons.
        local tabButton = ...;
        if (type(tabButton) ~= "table") then
            error("Bad argument #2 to 'TSB_SkillLineFlash'. Expected a tab button object.", 2);
        end
        local tabFlash = _G[tabButton:GetName().."Flash"];
        if (tabFlash) then
            tabFlash:Hide();
        end
        -- Now let's clean up by hiding the whole flash container (for CPU efficiency) if no more tabs are flashing.
        local flashTabs = TSB_SkillLineFlash("getflashtabs");
        if (#flashTabs == 0) then
            TSB_SkillLineFlash("hidecontainer");
        end
    elseif (action == "stopalltabs") then
        -- Stop ALL flash frames from flashing, if they're still flashing... and hide the container.
        local flashTabs = TSB_SkillLineFlash("getflashtabs");
        for k,flashFrame in ipairs(flashTabs) do -- Hide all flash-textures.
            flashFrame:Hide();
        end
        TSB_SkillLineFlash("hidecontainer");
    elseif (action == "hidecontainer") then
        -- Hide the "flash layer" container.
        -- NOTE: This does NOT clear the flash-state of the individual buttons; any "flash"-tagged ones will flash again on "start".
        UIFrameFlashRemoveFrame(TSB_SpellBookTabFlashFrame); -- Stops flashing the container (but the container STAYS VISIBLE with 100% opacity).
        TSB_SpellBookTabFlashFrame:Hide(); -- Also hide the actual frame, so that we can no longer see the (now static, non-flashing) flash layers.
    elseif (action == "synctoblizzard") then
        -- Bonus feature: This is used by our "TSB_EnhanceBlizzardSpellbook" to make their Spellbook's flash-state always perfectly reflect ours.
        -- NOTE: We achieve all of this without setting any of their variables, which means that we're NOT causing ANY taint here. Phew!

        -- Turn off all of Blizzard's "flash layers" and their container.
        for tabNum=1, MAX_SKILLLINE_TABS do -- Loop over all of Blizzard's tabs (note no "TSB_" prefix; we use Blizzard's variable this time).
            _G["SpellBookSkillLineTab"..tabNum.."Flash"]:Hide();
        end
        UIFrameFlashRemoveFrame(SpellBookTabFlashFrame); -- Stops flashing the container (but the container STAYS VISIBLE with 100% opacity).
        SpellBookTabFlashFrame:Hide(); -- Also hide the actual frame, so that we can no longer see the (now static, non-flashing) flash layers.

        -- Sync the actual, correct flashing state from our much more advanced TinyBook flashing system.
        local needsFlash = false;
        if (SpellBookFrame:IsShown() and SpellBookFrame.bookType == BOOKTYPE_SPELL) then -- Only sync if they're VIEWING Blizzard's SPELLBOOK tab.
            local flashTabs = TSB_SkillLineFlash("getflashtabs");
            for k,flashFrame in ipairs(flashTabs) do
                local blizzardFlashFrame = _G[flashFrame:GetName():gsub("^TSB_", "")]; -- Removes "TSB_" prefix, to get Blizzard's equivalent frame.
                if (blizzardFlashFrame) then
                    needsFlash = true;
                    blizzardFlashFrame:Show(); -- Show the same Blizzard "flash layers" as our TinyBook state.
                end
            end
        end

        -- If we've detected any flash layers that now need to be shown, start flashing their container frame.
        if (needsFlash) then
            -- NOTE: This is safe to call multiple times. It simply ignores calls if already flashing a specific frame reference.
            -- NOTE: We use "-1" as duration (flash forever (until clicked to stop)), unlike Blizzard's spellbook code which uses "30" seconds.
            UIFrameFlash(SpellBookTabFlashFrame, 0.5, 0.5, -1, nil); -- NOTE: This also makes the frame visible if it was hidden.
        end
    else
        error(format("Bad argument #1 to 'TSB_SkillLineFlash'. Received: \"%s\".", tostring(action)), 2);
    end
end

------
-- Updating Spellbook GUI
------

-- Main update function which refreshes most aspects of the spellbook frame.
-- NOTE: Optionally tells all spell-buttons to update their displayed data.
function TSB_SpellBookFrame_Update(updateSpellButtons)
    -- Assign text and visibility for bottom-tabs ("Spellbook" and "Pet" tabs).
    local hasPet, petToken = HasPetSpells();
    if (hasPet) then
        TSB_SpellBookFrameTabButton1:Show(); -- Spellbook tab.
        TSB_SpellBookFrameTabButton2:SetText(_G["PET_TYPE_"..petToken]); -- NOTE: Global strings: "PET_TYPE_PET = Pet, PET_TYPE_DEMON = Demon".
        TSB_SpellBookFrameTabButton2:Show(); -- Pet tab.
        TSB_SpellBookFrameTabButton3:Hide(); -- Third (always unused) tab.
    else
        -- Hide all bottom-tabs since there is no pet.
        TSB_SpellBookFrameTabButton1:Hide();
        TSB_SpellBookFrameTabButton2:Hide();
        TSB_SpellBookFrameTabButton3:Hide();
    end

    -- Disable the ACTIVE bottom-tab (either Spells or Pet), and enable the other.
    if (hasPet) then
        local tabNum = TSB_FRAME_TAB_LIST[TSB_SpellBookFrame.bookType];
        local tabButton;
        for i=1, 2 do
            tabButton = _G["TSB_SpellBookFrameTabButton"..i];
            if (i ~= tabNum) then
                tabButton:Enable();
            else
                tabButton:Disable();
            end
        end
    end

    -- Ensure that the "Switch between Blizzard/TinyBook spellbook" tabs are in the correct positions.
    TSB_RePosition_FrameTab4();

    -- Hide the "spell school" (skill line) tabs if not viewing the spellbook; otherwise update/show the tabs.
    if (TSB_SpellBookFrame.bookType ~= BOOKTYPE_SPELL) then
        TSB_SpellBookFrame_HideSkillTabs(); -- Pet spells have no separate "spell school" tabs, so hide them...
    else
        TSB_SpellBookFrame_UpdateSkillTabs(); -- Update spell school tabs and mark their active selection.
    end

    -- Change the main title of the window to either "Spellbook" or "Pet" (can also be "Demon") based on what tab is active.
    if (hasPet and TSB_SpellBookFrame.bookType == BOOKTYPE_PET) then
        TSB_SpellBookTitleText:SetText(_G["PET_TYPE_"..petToken]); -- NOTE: Global strings: "PET_TYPE_PET = Pet, PET_TYPE_DEMON = Demon".
    else
        TSB_SpellBookTitleText:SetText(SPELLBOOK); -- NOTE: "SPELLBOOK" is a global string: "Spellbook".
    end

    -- Rebuild the compact spell list, update pagination status, and optionally tell all spellbuttons to update their displayed data.
    TSB_SpellBookFrame_UpdatePage(updateSpellButtons);
end

-- Updates the pagination status (page number, and which pagination buttons are usable).
-- NOTE: Optionally tells all spell-buttons to update their displayed data.
-- NOTE: This function ALWAYS rebuilds the compact spell list, to guarantee that the visible page always uses the latest spell data.
function TSB_SpellBookFrame_UpdatePage(updateSpellButtons)
    -- Close the "spell rank flyout" if it's open, since we're now going to update the whole page contents.
    -- NOTE: Not REALLY necessary, since it should already have closed when they hovered over the button that caused the "UpdatePage" call.
    if (TSB_RankViewer_Close) then -- NOTE: Protects us during early calls, when the "RankViewer" code may not have been loaded yet.
        TSB_RankViewer_Close();
    end

    -- Rebuild the compact spell list with the freshest data from the current "spell school" (or "pet" book).
    -- NOTE: This also affects the page count that "TSB_SpellBook_GetCurrentPage" will return.
    TSB_RebuildSpellList();

    -- Retrieve the current page number, enable the allowed pagination buttons, and set the page counter text.
    local currentPage, maxPage = TSB_SpellBook_GetCurrentPage();
    if (currentPage == 1) then
        TSB_SpellBookPrevPageButton:Disable();
    else
        TSB_SpellBookPrevPageButton:Enable();
    end
    if (currentPage == maxPage) then
        TSB_SpellBookNextPageButton:Disable();
    else
        TSB_SpellBookNextPageButton:Enable();
    end
    TSB_SpellBookPageText:SetFormattedText(PAGE_NUMBER, currentPage); -- NOTE: "PAGE_NUMBER" is a global string: "Page %d".

    -- Tell the spell buttons to update their data to show the page's contents.
    if (updateSpellButtons) then
        -- NOTE: "UpdateSpells" ensures all spell-data in player's whole spellbook is loaded into the client, and ALWAYS fires "SPELLS_CHANGED"
        -- after execution (synchronously). Our spellbuttons in turn react to that event signal and update their displayed data!
        -- UPDATE: Actually, this method (used by Blizzard) is buggy and poorly thought out (in their code). We're NOT going to repeat their mistake!
        --UpdateSpells(); -- A terrible idea by Blizzard (tm). ;-)

        -- Directly update each individual spell button. (This is our replacement for Blizzard's technique; NO risk of recursive event-duplicates!)
        for k,btn in ipairs(TSB_AllSpellButtons) do
            TSB_SpellButton_UpdateButton(btn);
        end
    end
end

-- Hides the "spell school" tabs.
-- NOTE: Only used internally by "TSB_SpellBookFrame_Update".
function TSB_SpellBookFrame_HideSkillTabs()
    for i=1, TSB_MAX_SKILLLINE_TABS do
        _G["TSB_SpellBookSkillLineTab"..i]:Hide();
    end
end

-- Updates and shows the "spell school" tabs, and properly marks the selected school.
-- NOTE: Only used internally by "TSB_SpellBookFrame_Update".
function TSB_SpellBookFrame_UpdateSkillTabs()
    local numSkillLines = GetNumSpellTabs(); -- How many "spell school" tabs the player has; we always expect "4" here (General + 3 talent schools).
    local name, texture;
    local skillLineTab;
    for i=1, TSB_MAX_SKILLLINE_TABS do
        skillLineTab = _G["TSB_SpellBookSkillLineTab"..i];
        if (i <= numSkillLines and TSB_SpellBookFrame.bookType == BOOKTYPE_SPELL) then
            name, texture = GetSpellTabInfo(i);
            skillLineTab:SetNormalTexture(texture);
            skillLineTab.tooltip = name;
            skillLineTab:Show();

            -- Mark the active "spell school" as the selected tab.
            if (TSB_SpellBookFrame.selectedSkillLine == i) then
                skillLineTab:SetChecked(1);
            else
                skillLineTab:SetChecked(nil);
            end
        else
            skillLineTab:Hide();
        end
    end
end

-- Positions the "Switch between Blizzard/TinyBook spellbook" tabs at their correct offsets.
local posBlizzTab4, posTinyTab4; -- Tab position cache, for extra efficiency.
function TSB_RePosition_FrameTab4()
    -- If the GUI is in combat lockdown, we aren't able to SetPoint (or even Hide) these SecureTemplate frames, so just ignore the call.
    if (TSB_CombatLockdown.inCombat) then
        return;
    end

    -- We'll place the tabs at an offset that's based on whether we have a pet or not.
    -- NOTE: The reason we check if the buttons exist before we move them is because they may not be fully loaded during the earliest calls.
    -- NOTE: We cache the new positions to avoid frivolously calling "SetPoint", since "TSB_RePosition_FrameTab4" is called a lot.
    local yOffset = (HasPetSpells() and 36 or 61);
    if (SpellBookFrameTabButton4 and posBlizzTab4 ~= yOffset) then
        SpellBookFrameTabButton4:SetPoint("CENTER", SpellBookFrame, "BOTTOMLEFT", 79, yOffset);
        posBlizzTab4 = yOffset;
    end
    if (TSB_SpellBookFrameTabButton4 and posTinyTab4 ~= yOffset) then
        TSB_SpellBookFrameTabButton4:SetPoint("CENTER", TSB_SpellBookFrame, "BOTTOMLEFT", 79, yOffset);
        posTinyTab4 = yOffset;
    end
end

------
-- Spell Buttons
------

function TSB_SpellButton_OnLoad(self)
    -- Register mouse events, and set up the non-changing secure frame attributes.
    self:RegisterForDrag("LeftButton");
    self:RegisterForClicks("LeftButtonUp", "RightButtonUp");

    self:SetAttribute("type*", "spell");
    self:SetAttribute("CHATLINK-spell", ATTRIBUTE_NOOP);
    self:SetAttribute("PICKUPACTION-spell", ATTRIBUTE_NOOP);

    -- Add the SpellButton to the list of all buttons.
    -- NOTE: This is what we use INSTEAD of Blizzard's own spellbook's braindead (and buggy) "SPELLS_CHANGED" system.
    TSB_AllSpellButtons[#TSB_AllSpellButtons+1] = self;
end

function TSB_SpellButton_OnShow(self)
    -- Register events when visible (usable).
    --self:RegisterEvent("SPELLS_CHANGED"); -- DISABLED: We no longer use Blizzard's "SPELLS_CHANGED" idea.
    self:RegisterEvent("SPELL_UPDATE_COOLDOWN");
    self:RegisterEvent("CURRENT_SPELL_CAST_CHANGED");
    self:RegisterEvent("CRAFT_SHOW");
    self:RegisterEvent("CRAFT_CLOSE");
    self:RegisterEvent("TRADE_SKILL_SHOW");
    self:RegisterEvent("TRADE_SKILL_CLOSE");
    self:RegisterEvent("PET_BAR_UPDATE");

    TSB_SpellButton_UpdateButton(self);
end

function TSB_SpellButton_OnHide(self)
    -- Unregister events when invisible (not usable), to ensure zero processing power is wasted while the spellbook is hidden.
    -- NOTE: These buttons are parented to TSB_SpellBookFrame, which means that whenever the spellbook hides,
    -- all of these spell-buttons will hide and unregister properly!
    --self:UnregisterEvent("SPELLS_CHANGED"); -- DISABLED: We no longer use Blizzard's "SPELLS_CHANGED" idea.
    self:UnregisterEvent("SPELL_UPDATE_COOLDOWN");
    self:UnregisterEvent("CURRENT_SPELL_CAST_CHANGED");
    self:UnregisterEvent("CRAFT_SHOW");
    self:UnregisterEvent("CRAFT_CLOSE");
    self:UnregisterEvent("TRADE_SKILL_SHOW");
    self:UnregisterEvent("TRADE_SKILL_CLOSE");
    self:UnregisterEvent("PET_BAR_UPDATE");
end

function TSB_SpellButton_OnEvent(self, event, ...)
    -- If the GUI is in combat lockdown, save the event in a queue for later processing instead...
    if (TSB_CombatLockdown.inCombat) then
        TSB_EventQueue:addEvent(TSB_SpellButton_OnEvent, self, event, ...);
        return;
    end

    local arg1 = ...; -- Extract relevant args from varargs.
    --if (event == "SPELLS_CHANGED" or event == "SPELL_UPDATE_COOLDOWN") then -- DISABLED: We no longer use Blizzard's "SPELLS_CHANGED" idea.
    if (event == "SPELL_UPDATE_COOLDOWN") then
        TSB_SpellButton_UpdateButton(self);
    elseif (event == "CURRENT_SPELL_CAST_CHANGED") then
        TSB_SpellButton_UpdateSelection(self);
    elseif (event == "CRAFT_SHOW" or event == "CRAFT_CLOSE" or event == "TRADE_SKILL_SHOW" or event == "TRADE_SKILL_CLOSE") then
        TSB_SpellButton_UpdateSelection(self);
    elseif (event == "PET_BAR_UPDATE") then
        if (TSB_SpellBookFrame.bookType == BOOKTYPE_PET) then
            TSB_SpellButton_UpdateButton(self);
        end
    end
end

function TSB_SpellButton_OnEnter(self)
    -- When entered, show the spell's tooltip and show the lower ranks if any exist.
    local spellId, lowestId = TSB_GetSpellID(self);
    if (spellId == BAD_SPELL_ID) then
        return;
    end
    GameTooltip:SetOwner(self, "ANCHOR_RIGHT");
    if (GameTooltip:SetSpell(spellId, TSB_SpellBookFrame.bookType)) then
        self.UpdateTooltip = TSB_SpellButton_OnEnter;
    else
        self.UpdateTooltip = nil;
    end
    if (spellId ~= lowestId) then -- If this spell has multiple ranks... show the "spell ranks" flyout.
        -- NOTE: This function won't do anything in combat lockdown. However, we shouldn't even be HERE in "OnEnter" if we're in combat! ;-)
        TSB_RankViewer_ShowAllRanks(self, lowestId, spellId, TSB_SpellBookFrame.bookType);
    end
end


function TSB_SpellButton_OnLeave(self)
    -- Hide the tooltip when the player leaves the spellbutton, but do not hide the "RankViewer" frame.
    -- NOTE: The "RankViewer" is instead hidden by TSB_SpellBookFrame's "OnShow", "OnHide" and "OnLeave" (which triggers when mousing away
    -- from the spellbook OR when mousing over mouse-enabled elements (ie. buttons) on the spellbook frame (which acts like leaving the frame)).
    GameTooltip:Hide();
end

function TSB_SpellButton_PostClick(self, button)
    -- "PostClick" runs AFTER the normal "OnClick" handler (which belongs to the Secure Button in this case),
    -- and lets us process "modified" clicks that were ignored by "OnClick". This is how we're able to react
    -- to "special" clicks without tainting the spell-cast-capable OnClick handler of our own secure button!
    local spellId = TSB_GetSpellID(self);
    if (spellId == BAD_SPELL_ID) then
        return;
    end
    if (IsModifiedClick("CHATLINK")) then
        if (MacroFrame and MacroFrame:IsShown()) then
            local spellName, subSpellName = GetSpellName(spellId, TSB_SpellBookFrame.bookType);
            if (spellName and not IsPassiveSpell(spellId, TSB_SpellBookFrame.bookType)) then
                -- NOTE: Unlike the "TSB_RankViewer", we will ONLY insert the spell name (without the "(Rank X)" suffix),
                -- thus ensuring that we're inserting the "always max rank" version of the spell into the macro.
                -- However, IF the user wants to explicitly link to the rank, they should click the rank-frame version instead.
                ChatEdit_InsertLink(spellName);
            end
            return;
        else -- Regular chat frame.
            local spellLink = GetSpellLink(spellId, TSB_SpellBookFrame.bookType);
            if (spellLink) then
                ChatEdit_InsertLink(spellLink);
            end
            return;
        end
    end
    if (IsModifiedClick("PICKUPACTION")) then
        PickupSpell(spellId, TSB_SpellBookFrame.bookType);
        return;
    end
end

function TSB_SpellButton_OnDrag(self)
    -- When dragged, pick up the "real" spell ID that's attached to the button.
    local spellId = TSB_GetSpellID(self);
    if (spellId == BAD_SPELL_ID) then
        return;
    end
    if (not _G[self:GetName().."IconTexture"]:IsShown()) then
        return; -- NOTE: The "icon texture" being hidden means the button was disabled by us. Blizzard checks it this way too.
    end
    self:SetChecked(nil);
    PickupSpell(spellId, TSB_SpellBookFrame.bookType);
end

function TSB_SpellButton_UpdateSelection(self)
    -- Update "checked" (glowing outline) for the currently active "profession/crafting" spell-button.
    -- NOTE: The "IsSelectedSpell" API only returns true when spells such as Cooking, Beast Training, Smelting,
    -- and other professions are currently active (meaning their "crafting/choices"-window is OPEN). It does
    -- absolutely NOTHING else, and DOESN'T react to REGULAR SPELLS whatsoever; as tested by clicking, dragging,
    -- casting, channeling, toggling (such as enabling "Attack" (auto)), toggling auto-casting pet spells, etc.
    local spellId = TSB_GetSpellID(self);
    if (spellId ~= BAD_SPELL_ID and IsSelectedSpell(spellId, TSB_SpellBookFrame.bookType)) then
        self:SetChecked(1);
    else
        self:SetChecked(nil);
    end
end

function TSB_SpellButton_UpdateButton(self)
    -- NOTE: The code below uses "SetAttribute" which is forbidden (ignored) in combat. But we never call this in combat.

    -- Ensure that a "selected spell school" value exists...
    -- NOTE: Just a pretty pointless failsafe, which exists in this handler in the official Blizzard spellbook too.
    if (not TSB_SpellBookFrame.selectedSkillLine) then
        TSB_SpellBookFrame.selectedSkillLine = 1;
    end

    -- Before we proceed, ensure that the button's "ID offset" is within the amount of spells in our compact list,
    -- and that it doesn't exceed the total number of spells in that "school tab" (when counting all ranks).
    -- NOTE: The button's own ID is just a number from 1 to 12, which then gets increased by the page offset,
    -- to tell us which "spell" the button refers to "on the current page". This is how the buttons know which
    -- spell to render. And if we've reached the last page, the button's "ID + offset" math may point beyond
    -- the count of compact spells. In that case, "TSB_GetSpellID" will return BAD_SPELL_ID and we'll disable the btn.
    -- As for "SPELL_ID_TAB_MAX", it's just an extra failsafe which will NEVER be reached since our own compact list
    -- is always equal or lower than that number (depending on how many ranks we've squashed in the current tree).
    local spellId = TSB_GetSpellID(self);
    local name = self:GetName();
    local iconTexture = _G[name.."IconTexture"];
    local spellString = _G[name.."SpellName"];
    local subSpellString = _G[name.."SubSpellName"];
    local cooldown = _G[name.."Cooldown"];
    local autoCastableTexture = _G[name.."AutoCastable"];
    local autoCastModel = _G[name.."AutoCast"];
    if (spellId == BAD_SPELL_ID or spellId > SPELL_ID_TAB_MAX) then
        self:Disable();
        iconTexture:Hide();
        spellString:Hide();
        subSpellString:Hide();
        cooldown:Hide();
        autoCastableTexture:Hide();
        autoCastModel:Hide();
        self:SetChecked(nil);
        _G[name.."NormalTexture"]:SetVertexColor(1.0, 1.0, 1.0);
        return;
    else
        self:Enable();
    end

    -- Update the Button to reflect the current spell information.
    local texture = GetSpellTexture(spellId, TSB_SpellBookFrame.bookType);
    local highlightTexture = _G[name.."Highlight"];
    local normalTexture = _G[name.."NormalTexture"];

    local spellName, subSpellName = GetSpellName(spellId, TSB_SpellBookFrame.bookType);
    local fullName;
    if ((not subSpellName) or (strlen(subSpellName) == 0)) then
        fullName = spellName; -- "Some Spell"
    else
        fullName = spellName.."("..subSpellName..")"; -- "Some Spell(Rank 3)"
    end
    self:SetAttribute("spell", fullName);

    local start, duration, enable = GetSpellCooldown(spellId, TSB_SpellBookFrame.bookType);
    CooldownFrame_SetTimer(cooldown, start, duration, enable); -- Just modifies OUR "cooldown" object. Doesn't cause taint in Blizzard code.
    if (enable == 1) then
        iconTexture:SetVertexColor(1.0, 1.0, 1.0);
    else
        iconTexture:SetVertexColor(0.4, 0.4, 0.4);
    end

    local autoCastAllowed, autoCastEnabled = GetSpellAutocast(spellId, TSB_SpellBookFrame.bookType);
    if (autoCastAllowed) then
        -- Set "right-click" to run a macro to toggle pet autocast (that's safe since pet spells are the only kind that can autocast).
        -- NOTE: This is necessary because toggling autocast is a protected API, but we can achieve it via this "secure button" macro instead.
        self:SetAttribute("type2", "macro");
        self:SetAttribute("macrotext", "/petautocasttoggle "..fullName);
        autoCastableTexture:Show();
    else
        -- Reset "right-click" to regular "cast spell" action, exactly like right-clicks in the standard spellbook.
        self:SetAttribute("type2", "spell");
        autoCastableTexture:Hide();
    end
    if (autoCastEnabled) then
        autoCastModel:Show();
    else
        autoCastModel:Hide();
    end

    local isPassive = IsPassiveSpell(spellId, TSB_SpellBookFrame.bookType);
    if (isPassive) then
        normalTexture:SetVertexColor(0, 0, 0);
        highlightTexture:SetTexture("Interface\\Buttons\\UI-PassiveHighlight");
        --subSpellName = PASSIVE_PARENS; -- This would use the word "(Passive)" (instead of "Passive") but was commented out in Blizzard's spellbook too.
        spellString:SetTextColor(PASSIVE_SPELL_FONT_COLOR.r, PASSIVE_SPELL_FONT_COLOR.g, PASSIVE_SPELL_FONT_COLOR.b);
    else
        normalTexture:SetVertexColor(1.0, 1.0, 1.0);
        highlightTexture:SetTexture("Interface\\Buttons\\ButtonHilight-Square");
        spellString:SetTextColor(NORMAL_FONT_COLOR.r, NORMAL_FONT_COLOR.g, NORMAL_FONT_COLOR.b);
    end

    iconTexture:SetTexture(texture);
    spellString:SetText(spellName);
    subSpellString:SetText(subSpellName);
    if (subSpellName and strlen(subSpellName) > 0) then
        spellString:SetPoint("LEFT", self, "RIGHT", 4, 4);
    else
        spellString:SetPoint("LEFT", self, "RIGHT", 4, 2);
    end

    iconTexture:Show();
    spellString:Show();
    subSpellString:Show();
    TSB_SpellButton_UpdateSelection(self);
end

------
-- Spell Indexing
------

function TSB_GetSpellID(self)
    -- Figure out the REAL spell ID (for the "compact offset"), or return a "BAD_SPELL_ID" if we can't find that spell.
    -- NOTE: This function CAN be asked about invalid IDs/offsets, since we calculate the lookup-offset based on button-index and page-count.
    if (not self) then return BAD_SPELL_ID; end -- Ensure that an object was provided.
    local btnId = self:GetID(); -- The ID of the spell-button itself (on the GUI); ranges from 1 to 12 (the twelve buttons on the GUI).
    if (type(btnId) ~= "number") then return BAD_SPELL_ID; end -- Ensure that the object's "ID" property holds a number.

    -- Calculate the button's "spell slot offset" (basically, array offset) within the current spellbook "school tab" and its active page.
    local currentPage, maxPage = TSB_SpellBook_GetCurrentPage();
    local btnSpellOffsetID = btnId + (TSB_SPELLS_PER_PAGE * (currentPage - 1));

    -- Determine whether the ID (array offset) is actually valid for our compact spell array, or if it's out of range.
    if (btnSpellOffsetID < 1 or -- Our compact spell list starts at index 1, so just ensure that we're not being asked about 0 or lower.
        btnSpellOffsetID > SPELL_ID_LIST_COUNT) then -- Higher button offset ID than the number of spells we have in our compact SPELL_ID_LIST.
        return BAD_SPELL_ID;
    else -- Return the REAL spell slot ID (as expected by WoW client) from our compact SPELL_ID_LIST table (which only has the highest ranks).
        -- 1st return value: The REAL spell ID for the "highest rank spell" (from our compact SPELL_ID_LIST).
        -- 2nd return value: "Slot ID of highest rank of previous spell, plus 1", meaning THIS spell's lowest rank ID. Can be same as 1st ret val.
        -- NOTE: The 2nd return value is correct even for the [1] (first) offset, because SPELL_ID_LIST has the "spell school's start offset" in [0].
        -- NOTE: We DON'T check if the final return is within Blizzard's 1-1024 (TSB_MAX_SPELLS) range, since our compact list was built cleanly.
        return SPELL_ID_LIST[btnSpellOffsetID], (SPELL_ID_LIST[btnSpellOffsetID-1]+1);
    end
end

-- Forcibly turn TSB_GetSpellID into a global too, so that 3rd party addons can check what spells are on the TinyBook buttons.
-- NOTE: This is necessary because we made the variable into a local at the top of this file, to speed up access within this file.
_G.TSB_GetSpellID = TSB_GetSpellID; -- Make a global variable too.

-- Checks whether a spell-ID variable is legally usable in Blizzard's APIs such as "GetSpellName" (without them throwing errors).
-- NOTE: You don't have to use this on the return-value of TSB_GetSpellID, since that function ALWAYS returns legal IDs.
-- NOTE: This is a good place to document the fact that Blizzard's spell IDs go from 1-1024, and that if you try to look up a non-number,
-- or 0, or 1025, or nil, then their functions (such as "GetSpellName") will throw an error. If you try to look up a slot which simply doesn't
-- have a spell (such as "1000" when you just have "50" spells), then their APIs will gracefully return "nil". If you try to provide a float,
-- then it gets floored, except if it's less than 1 (but > 0) in which case it gets rounded up instead: 0 = 0 (invalid), 0.1 = 1, 0.9999 = 1,
-- 1.99999 = 1, and 1024.9999 = 1024. So in terms of "ID validity", you don't have to worry about whether the number could be a float.
-- NOTE: Technically, Blizzard's APIs also accept numeric strings ("1.1" = 1.1 = 1), but that's insane and we'll never use string-IDs in OUR code.
function TSB_IsLegalSpellID(spellId)
    return (type(spellId) == "number" and spellId >= 1 and spellId <= TSB_MAX_SPELLS);
end

-- Rather than listing every rank of every spell in our spellbook, we just build a compact spell list instead,
-- which only contains the highest ranks of each spell. And we offer a hover-menu to access the lower ranks.
-- NOTE: This function is called very often, so it would be pointless to rebuild the player's WHOLE spell list.
-- Instead, we ONLY build a cache for the currently viewed spell-school/tab, for maximum efficiency.
function TSB_RebuildSpellList()
    -- Determine the active tab's start-offset and how many spells it contains.
    local _, offset, numSpells;
    if (TSB_SpellBookFrame.bookType == BOOKTYPE_PET) then
        -- The Pet book does not have "spell school" tabs, just a single book, so it doesn't have any start-offset.
        offset = 0;
        numSpells = HasPetSpells(); -- Is nil if no pet, otherwise a number (how many pet spells we have).
    else
        -- Get info about the selected "spell school" tab.
        -- NOTE: Each tab has an offset which is added to all spell-slot IDs within that tab to get their true spell slot ID.
        -- The offset is actually the "slot ID" of the last spell on the PRECEDING spell-school tabs (if any), or 0 if there are no previous tabs.
        _, _, offset, numSpells = GetSpellTabInfo(TSB_SpellBookFrame.selectedSkillLine);
    end

    -- Empty the existing spell list.
    -- NOTE: We don't simply create a new table, since this function is called a lot and would cause a lot of garbage collection;
    -- instead, we wipe all values from the table (using "pairs" to guarantee that EVERY key is deleted) and then re-use the table.
    for k in pairs(SPELL_ID_LIST) do
        SPELL_ID_LIST[k] = nil;
    end

    -- Empty the existing spell list and build a new list for the current "spell school" tab.
    if (numSpells and numSpells >= 1) then -- Only scan if we have a non-nil, positive amount of spells in the given spell school/tab...
        local previousSpellName, currentSpellName;
        SPELL_ID_TAB_MAX = offset + numSpells; -- Tab's slot offset + how many spells that tab has; determines maximum valid slot ID (inclusive) on that tab.
        for spellSlotID=(offset+1), SPELL_ID_TAB_MAX do -- The 1st slot on this tab is at "offset (which is all preceding tab's combined spell-counts) plus 1".
            -- NOTE: We don't check if spellSlotID is between 1 and 1024 (TSB_MAX_SPELLS) here, since "offset" and "numSpells" came from Blizzard's APIs.
            currentSpellName = GetSpellName(spellSlotID, TSB_SpellBookFrame.bookType);
            if (currentSpellName) then -- Only proceed if a valid spell exists in that spellSlotID...
                if (previousSpellName ~= nil and currentSpellName == previousSpellName) then -- Found higher rank of same spell as last iteration!
                    SPELL_ID_LIST[#SPELL_ID_LIST] = spellSlotID; -- Overwrite last table entry with higher rank's slot ID to "upgrade" it.
                else -- Previous spell is nil (if this is the first iteration) OR the names don't match... Which means a new spell!
                    SPELL_ID_LIST[#SPELL_ID_LIST+1] = spellSlotID; -- Append (add) current spell slot ID to end of table.
                end
                previousSpellName = currentSpellName;
            else -- We've somehow reached an empty slot ID... so there are no more spells in the book. As a failsafe, let's stop looping...
                break; -- PS: This should never happen! It's just a failsafe...
            end
        end
    end

    -- Keep the start-offset used for all spell IDs within the current spell-school tab.
    -- NOTE: Only necessary due to TSB_GetSpellID()'s return value calculations whenever it determines the "lowest rank slot ID" of the 1st spell slot!
    SPELL_ID_LIST[0] = offset; -- Saved within the 0th element which isn't used by Lua's table-"array" handling and won't disrupt "#count" operator.
    SPELL_ID_LIST_COUNT = #SPELL_ID_LIST; -- How many spells we've got within the compact list. Helps other code determine array bounds and page count.
end
