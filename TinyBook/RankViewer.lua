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
local GetSpellCooldown = GetSpellCooldown;
local GetSpellName = GetSpellName;
local GetSpellTexture = GetSpellTexture;

-- WoW Constants and Variables

local _; -- Common "temp" variable, localized to avoid tainting global space.

-- Built-in Lua Functions

local _G = _G; -- Global table: We frequently use it to dynamically lookup global variables.
local assert = assert;
local floor = floor;
local strlen = strlen;
local type = type;

-- Turn some of our Globals (other files) into Locals

local TSB_RankViewer; -- Used a LOT by most functions! Defined in XML, so THIS LOCAL VARIABLE is NIL until TSB_RankViewer_OnLoad assigns it.
local TSB_CombatLockdown = TSB_CombatLockdown; -- Used by tons of functions to check if we're allowed to modify frames or if we're in lockdown.
local TSB_EventQueue = TSB_EventQueue; -- Can sometimes be called very frequently while we're in combat.
local TSB_IsLegalSpellID = TSB_IsLegalSpellID; -- Helps us determine if the input spell ranks are legal spell IDs.

-- Turn some of our Globals (this file) into Locals
-- NOTE: By pre-declaring these names as local, any "X = 1" assignment or "function X()" will write to the LOCAL variable.

local TSB_SpellRankButton_GetSpellInfo; -- Called by EVERY function that needs to know what spell a button contains! NOTE: We'll make this a global TOO, to allow 3rd party access.
local TSB_SpellRankButton_UpdateButton; -- Called super frequently in response to all kinds of navigation and spell-related events.

------
-- Constants
------

local TSB_FLYOUT_ICONS_PER_ROW = 4; -- Show four icons per row.
local BOOKTYPE_PET = BOOKTYPE_PET; -- From Blizzard's UI.
local BOOKTYPE_SPELL = BOOKTYPE_SPELL; -- From Blizzard's UI.

------
-- RankViewer Frame
------

function TSB_RankViewer_OnLoad(self)
    TSB_RankViewer = self; -- NOTE: This assignment is necessary for making the global into a local (see top of this file).

    self.activeSpells = {}; -- Will hold "lowestRank", "highestRank" and "bookType".
    self.spellAnchor = nil;
end

function TSB_RankViewer_ShowAllRanks(spellButton, lowestRank, highestRank, bookType)
    assert(type(spellButton) == "table", "Bad argument #1 to 'TSB_RankViewer_ShowAllRanks' (table expected)");
    assert(type(lowestRank) == "number", "Bad argument #2 to 'TSB_RankViewer_ShowAllRanks' (number expected)");
    assert(type(highestRank) == "number", "Bad argument #3 to 'TSB_RankViewer_ShowAllRanks' (number expected)");
    assert(type(bookType) == "string", "Bad argument #4 to 'TSB_RankViewer_ShowAllRanks' (string expected)");

    assert(TSB_IsLegalSpellID(lowestRank), "Bad argument #2 to 'TSB_RankViewer_ShowAllRanks' (invalid spell rank value)");
    assert(TSB_IsLegalSpellID(highestRank), "Bad argument #3 to 'TSB_RankViewer_ShowAllRanks' (invalid spell rank value)");

    assert(lowestRank <= highestRank, "Lowest rank must be less than or equal to highest rank");

    assert(bookType == BOOKTYPE_SPELL or bookType == BOOKTYPE_PET, "Invalid book type");

    -- If the GUI is in combat lockdown, we aren't able to modify our SecureTemplate frames, so just ignore the call.
    if (TSB_CombatLockdown.inCombat) then
        return;
    end

    -- Detect whether the spells are being changed (if we aren't already configured for that exact range of spell IDs and book type).
    local changedSpells = false;
    if (TSB_RankViewer.activeSpells.lowestRank ~= lowestRank or
        TSB_RankViewer.activeSpells.highestRank ~= highestRank or
        TSB_RankViewer.activeSpells.bookType ~= bookType) then
        -- Remember the new settings.
        TSB_RankViewer.activeSpells.lowestRank = lowestRank;
        TSB_RankViewer.activeSpells.highestRank = highestRank;
        TSB_RankViewer.activeSpells.bookType = bookType;
        changedSpells = true;
    end

    -- Display and update all necessary spell rank buttons.
    local btn, btnNum, btnName, btnCreated;
    for spellId=lowestRank, highestRank do
        -- Fetch or create the spell button for this rank.
        btnNum = (spellId - lowestRank) + 1; -- Counts upwards from 1.
        btnName = "TSB_SpellRankButton"..btnNum;
        btnCreated = false;
        btn = _G[btnName];
        if (not btn) then -- If such a high rank's button doesn't exist yet, let's create it...
            btn = CreateFrame("CheckButton", btnName, TSB_RankViewer, "TSB_SpellRankButtonTemplate");
            local iconSize = btn:GetWidth(); -- NOTE: This value is 30, and is the Size attribute of "TSB_SpellRankButtonTemplate".
            local x = iconSize * ((btnNum - 1) % TSB_FLYOUT_ICONS_PER_ROW);
            local y = -(iconSize * floor((btnNum - 1) / TSB_FLYOUT_ICONS_PER_ROW));
            btn:SetPoint("TOPLEFT", TSB_RankViewer, "TOPLEFT", x, y);
            btn:SetID(btnNum); -- Give the button an ID based on its button-number.
            btnCreated = true;
        end

        -- Display the spell button, and ensure that it's enabled (if necessary).
        -- NOTE: NEVER assume that ":Hide" on pre-existing buttons has been called BEFORE this "TSB_RankViewer_ShowAllRanks".
        -- In particular, there's such a situation if you hover over a left-side spellbook icon, get a flyout, then move the
        -- mouse cursor OVER/VIA THE FLYOUT FRAME all the way to the right-side spellbook icon which also triggers a flyout. In
        -- that case, there's no triggering of the "Close" function for the flyout before we get told to open a flyout again.
        btn:Show();
        if (changedSpells or btnCreated) then
            -- NOTE: The reason why we only re-enable if "changedSpells" is to avoid clearing disabled-states that have been applied *after*
            -- the initial spell assignment to the button. Such as if the spell turned out to be invalid (no spell existing in that ID slot).
            btn:Enable();
        end

        -- Update button details such as the icon, rank text, active/ongoing cooldown timer, and which spell to cast if clicked.
        -- NOTE: The reason why we do this EVERY time (rather than just at creation/major updates), is MAINLY to ensure that the icon
        -- is always completely up-to-date with regards to things like spell cooldowns, etc. Otherwise it may display outdated information.
        -- NOTE: We COULD make a separate update-function which only handles the cooldown/whatever, but that's totally pointless
        -- since the FULL function we're calling here only takes ~1 millisecond IN TOTAL to update ALL spell rank buttons!
        TSB_SpellRankButton_UpdateButton(btn);

        -- Remove any lingering "highlight" glows (those can get "stuck" whenever the flyout is suddenly hidden while a button is highlighted).
        -- NOTE: There's no direct API to "stop highlighting". The GAME client handles it, and DOESN'T use Show/Hide, SetVertexColor,
        -- or SetAlpha. However, by telling the game to LOCK an object into "highlighted" state and then unlocking again, it goes away!
        btn:LockHighlight();
        btn:UnlockHighlight();
    end

    -- Hide and disable all unused spell rank buttons.
    repeat
        btnNum = btnNum + 1; -- Will look for the "next button".
        btnName = "TSB_SpellRankButton"..btnNum;
        btn = _G[btnName];
        if (btn) then
            btn:Disable();
            btn:Hide();
        end
    until (not btn);

    -- Position the flyout next to the button which originated the request.
    TSB_RankViewer.spellAnchor = spellButton; -- Remember which button we're anchored to (we're NOT parented to it).
    TSB_RankViewer:SetPoint("TOPLEFT", TSB_RankViewer.spellAnchor, "TOPRIGHT");
    TSB_RankViewer:Show();
end

function TSB_RankViewer_Close()
    -- NOTE: Blizzard doesn't allow us to hide the frame while in combat, since it's a parent for secure frames. However, that problem
    -- should never happen since TinyBook auto-hides at the moment combat starts, and WE'RE parented to it (and get hidden too). However,
    -- certain in-combat events (such as navigating Blizzard's spellbook which fires "SPELLS_CHANGED") may call "CloseAndForget" which
    -- would in turn call us, so we'll simply ignore any in-combat calls to hide. (And we're ALREADY hidden in combat, as mentioned.)
    if (not TSB_CombatLockdown.inCombat) then
        TSB_RankViewer:Hide(); -- NOTE: Hiding our frame also hides all spell-buttons since they're parented to us.
    end
end

function TSB_RankViewer_CloseAndForget()
    TSB_RankViewer_Close();

    -- Erase all information about the current buttons, to FORCE the button assignments to be updated on the next "ShowAllRanks" call.
    -- NOTE: This is mainly useful (and very important) to ensure that old spell offset IDs are forgotten when new spells are added/removed in spellbook.
    TSB_RankViewer.activeSpells.lowestRank = nil;
    TSB_RankViewer.activeSpells.highestRank = nil;
    TSB_RankViewer.activeSpells.bookType = nil;
end

------
-- Spell Buttons
------

function TSB_SpellRankButton_GetSpellInfo(self)
    assert(type(self) == "table", "Bad argument #1 to 'TSB_SpellRankButton_GetSpellInfo' (table expected)");

    local spellId, bookType;
    if (self and
        self.GetID and
        TSB_RankViewer.activeSpells.lowestRank and
        TSB_RankViewer.activeSpells.highestRank and
        TSB_RankViewer.activeSpells.bookType) then
        -- Calculate the spell's ID based on the lowest spell rank ID and the button's offset (+0, +1, +2, etc).
        spellId = TSB_RankViewer.activeSpells.lowestRank + (self:GetID() - 1);
        -- Ensure the result doesn't exceed the highest rank that we're displaying (in that case, we've been asked about an inactive button).
        if (spellId <= TSB_RankViewer.activeSpells.highestRank) then
            bookType = TSB_RankViewer.activeSpells.bookType; -- Also provide the book type.
        else
            spellId = nil; -- Reset back to nil, so that we return two nil values.
        end
    end

    return spellId, bookType; -- NOTE: If the 1st return value is non-nil, then you know the 2nd is non-nil too and that both are valid.
end

_G.TSB_SpellRankButton_GetSpellInfo = TSB_SpellRankButton_GetSpellInfo; -- Make a global variable too.

function TSB_SpellRankButton_OnLoad(self)
    -- Configure non-changing attributes.
    self:RegisterForDrag("LeftButton");
    self:RegisterForClicks("LeftButtonUp", "RightButtonUp");

    self:SetAttribute("type*", "spell");
    self:SetAttribute("CHATLINK-spell", ATTRIBUTE_NOOP);
    self:SetAttribute("PICKUPACTION-spell", ATTRIBUTE_NOOP);

    -- Run all registered "third-party addon support" callbacks for this button.
    -- NOTE: We do this here since these buttons are created dynamically, on-demand.
    for k,callback in ipairs(TSB_SpellBookFrame.thirdPartyHooks.rankButtons) do
        callback(self);
    end
end

function TSB_SpellRankButton_OnShow(self)
    -- Register events when visible (usable).
    -- NOTE: We DON'T run "TSB_SpellRankButton_UpdateButton" here; instead, we do that manually in other code locations, to GUARANTEE
    -- button updates, since this "OnShow" handler is UNRELIABLE (icons may already be visible when re-used, and then they won't "OnShow").
    self:RegisterEvent("SPELL_UPDATE_COOLDOWN");
end

function TSB_SpellRankButton_OnHide(self)
    -- Unregister events when invisible (not usable), to ensure zero processing power is wasted while the spellbook is hidden.
    -- NOTE: These buttons are parented to TSB_RankViewer, which in turn is parented to TSB_SpellBookFrame, which means
    -- that whenever the spellbook (or flyout) hides, all of these list-buttons will hide and unregister properly!
    self:UnregisterEvent("SPELL_UPDATE_COOLDOWN");
end

function TSB_SpellRankButton_OnEvent(self, event, ...)
    -- If the GUI is in combat lockdown, save the event in a queue for later processing instead...
    if (TSB_CombatLockdown.inCombat) then
        TSB_EventQueue:addEvent(TSB_SpellRankButton_OnEvent, self, event, ...);
        return;
    end

    -- NOTE: Spells in this "lower ranks" list frame only need their cooldown updated. No other events matter.
    local arg1 = ...; -- Extract relevant args from varargs.
    if (event == "SPELL_UPDATE_COOLDOWN") then
        TSB_SpellRankButton_UpdateButton(self);
    end
end

function TSB_SpellRankButton_OnEnter(self)
    -- When hovered, show the spell's tooltip.
    local spellId, bookType = TSB_SpellRankButton_GetSpellInfo(self);
    if (not spellId) then return; end

    GameTooltip:SetOwner(self, "ANCHOR_RIGHT");
    if (GameTooltip:SetSpell(spellId, bookType)) then -- NOTE: Returns nil if spell doesn't exist.
        self.UpdateTooltip = TSB_SpellRankButton_OnEnter;
    else
        self.UpdateTooltip = nil;
    end
end

function TSB_SpellRankButton_OnLeave(self)
    -- Hide the individual spell's tooltip when the player leaves the spellbutton, but do not hide the "RankViewer" frame.
    GameTooltip:Hide();
end

function TSB_SpellRankButton_PostClick(self, button)
    -- "PostClick" runs AFTER the normal "OnClick" handler (which belongs to the Secure Button in this case),
    -- and lets us process "modified" clicks that were ignored by "OnClick". This is how we're able to react
    -- to "special" clicks without tainting the spell-cast-capable OnClick handler of our own secure button!
    local spellId, bookType = TSB_SpellRankButton_GetSpellInfo(self);
    if (not spellId) then return; end

    if (IsModifiedClick("CHATLINK")) then
        if (MacroFrame and MacroFrame:IsShown()) then
            local spellName, subSpellName = GetSpellName(spellId, bookType); -- NOTE: Returns nil if spell doesn't exist.
            if (spellName and not IsPassiveSpell(spellId, bookType)) then -- NOTE: Returns nil if spell doesn't exist or not passive.
                if (subSpellName and (strlen(subSpellName) > 0)) then
                    ChatEdit_InsertLink(spellName.."("..subSpellName..")");
                else
                    ChatEdit_InsertLink(spellName);
                end
            end
            return;
        else -- Regular chat frame.
            local spellLink = GetSpellLink(spellId, bookType); -- NOTE: Returns nil if spell doesn't exist.
            if (spellLink) then
                ChatEdit_InsertLink(spellLink);
            end
            return;
        end
    end
    if (IsModifiedClick("PICKUPACTION")) then
        PickupSpell(spellId, bookType); -- NOTE: Returns nil (and does nothing except clear cursor contents) if spell doesn't exist.
        return;
    end
end

function TSB_SpellRankButton_OnDrag(self)
    -- When dragged, pick up the actual spell that's attached to the button.
    local spellId, bookType = TSB_SpellRankButton_GetSpellInfo(self);
    if (not spellId) then return; end

    self:SetChecked(nil);
    PickupSpell(spellId, bookType); -- NOTE: Returns nil (and does nothing except clear cursor contents) if spell doesn't exist.
end

function TSB_SpellRankButton_UpdateButton(self)
    -- NOTE: The code below uses "SetAttribute" which is forbidden (ignored) in combat. But we never call this in combat.

    -- Update spell button aspects such as its icon, cooldown-state, and tell it which spell to cast if clicked.
    local spellId, bookType = TSB_SpellRankButton_GetSpellInfo(self);
    if (not spellId) then
        -- If this button doesn't have a valid spell associated (within the "all ranks" ID range), then it shouldn't be visible anymore.
        -- NOTE: This is just a failsafe. We don't even run this function if the button doesn't have a valid spell.
        self:Disable();
        self:Hide();
        return;
    end

    local name = self:GetName();
    local iconTexture = _G[name.."IconTexture"];
    local rankString = _G[name.."RankName"];
    local cooldown = _G[name.."Cooldown"];

    -- Get the spell's texture, and use that opportunity to also verify that the spell actually exists.
    local texture = GetSpellTexture(spellId, bookType); -- NOTE: Returns nil if spell doesn't exist.
    if (not texture) then
        -- If the spell ID for this button doesn't refer to a real spell, then it means that we've been given bad parameters
        -- to "TSB_RankViewer_ShowAllRanks" (given valid spell IDs from 1-1024, but not referring to actual spells). We'll
        -- still display the spell rank button, but will instead replace its contents with some debugging information.
        self:Disable(); -- NOTE: Disables most interaction (ie. "OnLeave", clicking, highlighting, etc).
        iconTexture:Hide(); -- Ensure that the icon texture is hidden so that we just see a blank icon.
        rankString:SetText("|cFFFF77FF"..spellId); -- Show the spell ID in pink as the button text, useful for debugging.
        rankString:Show();
        cooldown:Hide();
        self:SetChecked(nil);
        --self:Hide(); -- NOTE: We don't hide the button completely, since that would prevent us from knowing about the error.
        return;
    end

    -- Determine the full spell name, including its rank suffix.
    local spellName, subSpellName = GetSpellName(spellId, bookType); -- NOTE: Returns nil if spell doesn't exist.
    local fullName;
    if ((not subSpellName) or (strlen(subSpellName) == 0)) then
        fullName = spellName; -- "Some Spell"
    else
        fullName = spellName.."("..subSpellName..")"; -- "Some Spell(Rank 3)"
    end
    self:SetAttribute("spell", fullName); -- Assign that exact spell name to the button for casting-purposes.

    -- Update "cooldown dimming" effect ("SetTimer" starts/clears the gradual, clockwise "wiping" of the dimming as the timer progress).
    local start, duration, enable = GetSpellCooldown(spellId, bookType); -- NOTE: Returns numeric values "0, 0, 1" if spell doesn't exist.
    CooldownFrame_SetTimer(cooldown, start, duration, enable); -- Just modifies OUR "cooldown" object. Doesn't cause taint in Blizzard code.
    if (enable == 1) then
        iconTexture:SetVertexColor(1.0, 1.0, 1.0);
    else
        iconTexture:SetVertexColor(0.4, 0.4, 0.4);
    end

    -- Extract the spell's rank numbers by grabbing the first encountered sequence of 1 or more digits.
    local rank = subSpellName and subSpellName:match("%d+"); -- NOTE: Is nil if no subSpellName or no digits in it.
    if (not rank) then rank = "?"; end

    -- Now just apply the texture and spell rank information to the button.
    iconTexture:SetTexture(texture);
    rankString:SetText(rank);
    iconTexture:Show();
    rankString:Show();
    self:SetChecked(nil); -- NOTE: Ensures button isn't in "checked" mode; same as "TSB_SpellButton_UpdateSelection".
end
